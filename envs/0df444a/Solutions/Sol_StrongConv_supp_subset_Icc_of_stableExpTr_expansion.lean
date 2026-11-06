-- Prove2me | solution 1 for StrongConv.supp_subset_Icc_of_stableExpTr_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:42:44.30394+00:00
-- url     : https://prove2.me/submissions/64eb96dd-e280-4794-a45c-f1a117aa95ca

import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_exists_linearization
import Theorems.Thm_StrongConv_supp_subset_Icc_limsup
import Mathlib
section
section
section
open Polynomial Filter Topology

noncomputable section

open scoped Classical

namespace StrongConv.S9

open StrongConv

/-! ## Padded periodic linearizations -/

/-- A periodic family of square `Dm × Dm` matrix coefficients: `B j l` is the coefficient of
`λ(g_l)` in the `j`-th factor `X_j`, with `X_{j+q} = X_j` (the paper's cyclic extension, after
padding the rectangular `D_j × D_{j+1}` blocks of Lemma 9.1 by zeros to a common size `Dm`). -/
structure Lin (d : ℕ) where
  q : ℕ
  hq : 1 ≤ q
  Dm : ℕ
  B : ℕ → Letter d → Matrix (Fin Dm) (Fin Dm) ℂ
  periodic : ∀ j l, B (j + q) l = B j l

variable {d : ℕ}

/-- `X_j = ∑_l B_{j,l} ⊗ λ(g_l)` on `Dm` copies of `ℓ²(F_d)`. -/
def Xop (L : Lin d) (j : ℕ) :
    PiLp 2 (fun _ : Fin L.Dm => L2Free d) →L[ℂ] PiLp 2 (fun _ : Fin L.Dm => L2Free d) :=
  linOp (L.B j)

/-- `X_1 X_2 ⋯ X_m`. -/
def Xprod (L : Lin d) (m : ℕ) :
    PiLp 2 (fun _ : Fin L.Dm => L2Free d) →L[ℂ] PiLp 2 (fun _ : Fin L.Dm => L2Free d) :=
  ((List.range m).map fun j => Xop L (j + 1)).prod

/-- `B_{1,i₁} B_{2,i₂} ⋯ B_{m,i_m}`. -/
def Bprod (L : Lin d) (m : ℕ) (i : Fin m → Letter d) : Matrix (Fin L.Dm) (Fin L.Dm) ℂ :=
  (List.ofFn fun j : Fin m => L.B ((j : ℕ) + 1) (i j)).prod

/-- `a_{i₁ … i_m} = tr_D (A_{1,i₁} ⋯ A_{m,i_m})`, as the trace of the padded product over `D`. -/
def aCoef (L : Lin d) (D m : ℕ) (i : Fin m → Letter d) : ℂ :=
  (D : ℂ)⁻¹ * (Bprod L m i).trace

/-- The padded blocks are supported in the top-left `D × D` corner at both ends of the chain. -/
def Lin.Supp (L : Lin d) (D : ℕ) : Prop :=
  (∀ l (a b : Fin L.Dm), D ≤ (a : ℕ) → L.B 1 l a b = 0) ∧
    (∀ l (a b : Fin L.Dm), D ≤ (b : ℕ) → L.B L.q l a b = 0)

/-- The exponent `k` of the non-power root of `u`: `u = v^k` (junk `0` if `u = 1`). -/
def rootExp (u : FreeGroup (Fin d)) : ℕ :=
  if h : ∃ v : FreeGroup (Fin d), ∃ k : ℕ, IsNonPower v ∧ 1 ≤ k ∧ u = v ^ k then
    Classical.choose (Classical.choose_spec h) else 0


end StrongConv.S9

end
end
end

section
section
set_option autoImplicit true
open Polynomial Filter Topology

noncomputable section

open scoped Classical

namespace StrongConv.S9.PartR

open StrongConv FreeGroup FreeGroup.reduceCyclically

/-! ### Copied from S5 PartRoot -/

lemma length_toWord_pow_ge {d : ℕ} (v : FreeGroup (Fin d)) (hv : v ≠ 1) (k : ℕ) :
    k ≤ (v ^ k).toWord.length := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hr : reduceCyclically v.toWord ≠ [] := by
    intro h
    apply hv
    have := congr_arg FreeGroup.mk (conj_conjugator_reduceCyclically v.toWord)
    rw [mk_toWord, h, List.append_nil, ← mul_mk, ← inv_mk, mul_inv_cancel] at this
    exact this.symm
  have hw : (v ^ k).toWord = conjugator v.toWord ++
      (List.replicate k (reduceCyclically v.toWord)).flatten ++ invRev (conjugator v.toWord) := by
    rw [toWord_pow, reduce_flatten_replicate isReduced_toWord, if_neg hk.ne']
  rw [hw]
  simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul]
  have : 1 ≤ (reduceCyclically v.toWord).length := List.length_pos_iff.mpr hr
  nlinarith

theorem exists_nonpower_pow {d : ℕ} (g : FreeGroup (Fin d)) (hg : g ≠ 1) :
    ∃ (v : FreeGroup (Fin d)) (k : ℕ), IsNonPower v ∧ 1 ≤ k ∧ g = v ^ k := by
  classical
  let B := g.toWord.length
  let P : ℕ → Prop := fun k => ∃ v : FreeGroup (Fin d), g = v ^ k
  have hbound : ∀ k, P k → k ≤ B := by
    rintro k ⟨v, hv⟩
    have hv1 : v ≠ 1 := by rintro rfl; exact hg (by simpa using hv)
    have := length_toWord_pow_ge v hv1 k
    rw [← hv] at this
    exact this
  have hP1 : P 1 := ⟨g, by simp⟩
  have h1B : 1 ≤ B := hbound 1 hP1
  set k := Nat.findGreatest P B with hk
  have hPk : P k := Nat.findGreatest_spec h1B hP1
  have hk1 : 1 ≤ k := Nat.le_findGreatest h1B hP1
  obtain ⟨v, hv⟩ := hPk
  refine ⟨v, k, ⟨?_, ?_⟩, hk1, hv⟩
  · rintro rfl; exact hg (by simpa using hv)
  · intro u m hm hvu
    have hPkm : P (k * m) := ⟨u, by rw [hv, hvu, ← pow_mul, mul_comm]⟩
    have hle : k * m ≤ k := Nat.le_findGreatest (hbound _ hPkm) hPkm
    nlinarith

/-! ### Periodic words -/

lemma period_pow {α : Type*} (m : ℕ) : ∀ (w : List α) (p : ℕ), 0 < p → w.length = p * m →
    List.HasPeriod w p → w = (List.replicate m (w.take p)).flatten := by
  induction m with
  | zero =>
    intro w p _ hl _
    simp at hl
    simp [hl]
  | succ m ih =>
    intro w p hp hl hper
    have hlp : p ≤ w.length := by rw [hl]; nlinarith
    have hdl : (w.drop p).length = p * m := by
      rw [List.length_drop, hl]; rw [mul_add, mul_one]; omega
    have hper' : List.HasPeriod (w.drop p) p := by
      have : List.HasPeriod (w.take p ++ w.drop p ++ []) p := by simpa using hper
      exact this.factor
    have h1 := ih (w.drop p) p hp hdl hper'
    have h2 : m ≠ 0 → (w.drop p).take p = w.take p := by
      intro hm
      obtain ⟨z, hz⟩ := hper.drop_prefix
      have hpl : p ≤ (w.drop p).length := by rw [hdl]; nlinarith [Nat.pos_of_ne_zero hm]
      conv_rhs => rw [← hz]
      exact (List.take_append_of_le_length hpl).symm
    rw [List.replicate_succ, List.flatten_cons]
    conv_lhs => rw [← List.take_append_drop p w]
    congr 1
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa using h1
    · rw [h1, h2 hm.ne']

lemma hasPeriod_flatten {α : Type*} (c : List α) (k : ℕ) :
    List.HasPeriod (List.replicate k c).flatten c.length := by
  unfold List.HasPeriod
  rcases k with _ | k
  · simp
  · have e1 : ((List.replicate (k + 1) c).flatten).take c.length = c := by
      simp [List.replicate_succ]
    rw [e1]
    have e2 : c ++ (List.replicate (k + 1) c).flatten = (List.replicate (k + 1) c).flatten ++ c := by
      rw [← List.flatten_cons, ← List.replicate_succ, List.replicate_succ' (n := k + 1),
        List.flatten_concat]
    rw [e2]
    exact List.prefix_append _ _

lemma prefix_flatten {α : Type*} (c : List α) (k : ℕ) (hk : 1 ≤ k) :
    c <+: (List.replicate k c).flatten := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : k ≠ 0)
  rw [List.replicate_succ, List.flatten_cons]
  exact List.prefix_append _ _

lemma mk_flatten {d : ℕ} (c : List (Fin d × Bool)) (k : ℕ) :
    FreeGroup.mk (List.replicate k c).flatten = (FreeGroup.mk c) ^ k := by
  induction k with
  | zero => simp; rfl
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, ← mul_mk, ih, pow_succ']


/-! ### Cyclic decomposition -/

lemma cyc_ne_nil {d : ℕ} (v : FreeGroup (Fin d)) (hv : v ≠ 1) :
    reduceCyclically v.toWord ≠ [] := by
  intro h
  apply hv
  have := congr_arg FreeGroup.mk (conj_conjugator_reduceCyclically v.toWord)
  rw [mk_toWord, h, List.append_nil, ← mul_mk, ← inv_mk, mul_inv_cancel] at this
  exact this.symm

lemma toWord_pow_eq {d : ℕ} (v : FreeGroup (Fin d)) (m : ℕ) (hm : 1 ≤ m) :
    (v ^ m).toWord = conjugator v.toWord ++
      (List.replicate m (reduceCyclically v.toWord)).flatten ++ invRev (conjugator v.toWord) := by
  rw [toWord_pow, reduce_flatten_replicate isReduced_toWord, if_neg (by omega)]

lemma eq_conj {d : ℕ} (v : FreeGroup (Fin d)) :
    v = mk (conjugator v.toWord) * mk (reduceCyclically v.toWord) * (mk (conjugator v.toWord))⁻¹ := by
  have := congr_arg FreeGroup.mk (conj_conjugator_reduceCyclically v.toWord)
  rw [mk_toWord, ← mul_mk, ← mul_mk, ← inv_mk] at this
  exact this.symm

lemma nonpower_core {d : ℕ} (v : FreeGroup (Fin d)) (hv : IsNonPower v) (m : ℕ)
    (s : List (Fin d × Bool)) (hc : reduceCyclically v.toWord = (List.replicate m s).flatten) :
    m = 1 := by
  have hne := cyc_ne_nil v hv.1
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hc
    exact hne hc
  by_contra hm1
  have h2 : 2 ≤ m := by omega
  apply hv.2 (mk (conjugator v.toWord) * mk s * (mk (conjugator v.toWord))⁻¹) m h2
  rw [conj_pow, ← mk_flatten, ← hc]
  exact eq_conj v

theorem root_unique (v v' : FreeGroup (Fin d)) (k k' : ℕ) (hv : IsNonPower v)
    (hv' : IsNonPower v') (hk : 1 ≤ k) (hk' : 1 ≤ k') (h : v ^ k = v' ^ k') : k = k' := by
  set g := conjugator v.toWord with hg
  set c := reduceCyclically v.toWord with hc
  set g' := conjugator v'.toWord with hg'
  set c' := reduceCyclically v'.toWord with hc'
  have hcne : c ≠ [] := cyc_ne_nil v hv.1
  have hcne' : c' ≠ [] := cyc_ne_nil v' hv'.1
  have hℓ : 1 ≤ c.length := List.length_pos_iff.mpr hcne
  have hℓ' : 1 ≤ c'.length := List.length_pos_iff.mpr hcne'
  have hw : ∀ j : ℕ, 1 ≤ j → g ++ (List.replicate (k * j) c).flatten ++ invRev g =
      g' ++ (List.replicate (k' * j) c').flatten ++ invRev g' := by
    intro j hj
    have hkj : 1 ≤ k * j := Nat.mul_pos hk hj
    have hkj' : 1 ≤ k' * j := Nat.mul_pos hk' hj
    rw [← toWord_pow_eq v _ hkj, ← toWord_pow_eq v' _ hkj', pow_mul, pow_mul, h]
  have e1 := hw 1 le_rfl
  have e2 := hw 2 (by norm_num)
  have l1 := congr_arg List.length e1
  have l2 := congr_arg List.length e2
  simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul, invRev_length] at l1 l2
  have hkl : k * c.length = k' * c'.length := by nlinarith
  have hgl : g.length = g'.length := by nlinarith
  simp only [mul_one] at e1
  have hfl : (g ++ (List.replicate k c).flatten).length = (g' ++ (List.replicate k' c').flatten).length := by
    simp only [List.length_append, List.length_flatten, List.map_replicate, List.sum_replicate,
      smul_eq_mul]
    omega
  obtain ⟨e3, -⟩ := List.append_inj e1 hfl
  obtain ⟨-, e4⟩ := List.append_inj e3 hgl
  -- e4 : c^k = c'^k'
  set C := (List.replicate k c).flatten with hC
  have hC' : (List.replicate k' c').flatten = C := e4.symm
  have hn : C.length = k * c.length := by
    simp [hC]
  have hper : List.HasPeriod C c.length := hasPeriod_flatten c k
  have hper' : List.HasPeriod C c'.length := by
    rw [← hC']; exact hasPeriod_flatten c' k'
  set G := Nat.gcd c.length c'.length with hG
  have hGpos : 0 < G := Nat.gcd_pos_of_pos_left _ hℓ
  have hlen : c.length + c'.length - G ≤ C.length := by
    have h1 : c.length ∣ C.length := ⟨k, by rw [hn]; ring⟩
    have h2 : c'.length ∣ C.length := ⟨k', by rw [hn, hkl]; ring⟩
    have h3 : Nat.lcm c.length c'.length ∣ C.length := Nat.lcm_dvd h1 h2
    have hCpos : 0 < C.length := by rw [hn]; nlinarith
    have h4 : Nat.lcm c.length c'.length ≤ C.length := Nat.le_of_dvd hCpos h3
    have h5 := Nat.gcd_mul_lcm c.length c'.length
    obtain ⟨a, ha⟩ := Nat.gcd_dvd_left c.length c'.length
    obtain ⟨b, hb⟩ := Nat.gcd_dvd_right c.length c'.length
    rw [← hG] at h5 ha hb
    have ha1 : 1 ≤ a := by
      by_contra hh
      have : a = 0 := by omega
      subst this
      rw [mul_zero] at ha
      omega
    have hb1 : 1 ≤ b := by
      by_contra hh
      have : b = 0 := by omega
      subst this
      rw [mul_zero] at hb
      omega
    have hlcm : Nat.lcm c.length c'.length = G * a * b := by
      apply Nat.eq_of_mul_eq_mul_left hGpos
      rw [h5, ha, hb]
      ring
    obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le' ha1
    obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le' hb1
    rw [hlcm] at h4
    have : G * (b' + 1) + G * (a' + 1) ≤ G * (a' + 1) * (b' + 1) + G := by
      have : 0 ≤ G * a' * b' := Nat.zero_le _
      nlinarith
    omega
  have hperG : List.HasPeriod C G := hper.gcd hper' hlen
  have hGc : G ∣ c.length := Nat.gcd_dvd_left _ _
  have hGc' : G ∣ c'.length := Nat.gcd_dvd_right _ _
  have hpc : List.HasPeriod c G := hperG.infix (prefix_flatten c k hk).isInfix
  have hpc' : List.HasPeriod c' G :=
    hperG.infix (by rw [← hC']; exact (prefix_flatten c' k' hk').isInfix)
  have hc1 := period_pow (c.length / G) c G hGpos (by rw [Nat.mul_div_cancel' hGc]) hpc
  have hc1' := period_pow (c'.length / G) c' G hGpos (by rw [Nat.mul_div_cancel' hGc']) hpc'
  have hm := nonpower_core v hv _ _ hc1
  have hm' := nonpower_core v' hv' _ _ hc1'
  have e5 : c.length = G := by
    have := Nat.mul_div_cancel' hGc
    rw [hm] at this; omega
  have e6 : c'.length = G := by
    have := Nat.mul_div_cancel' hGc'
    rw [hm'] at this; omega
  rw [e5, e6] at hkl
  exact Nat.eq_of_mul_eq_mul_right hGpos hkl

theorem root_exists (u : FreeGroup (Fin d)) (hu : u ≠ 1) :
    ∃ v : FreeGroup (Fin d), ∃ k : ℕ, IsNonPower v ∧ 1 ≤ k ∧ u = v ^ k :=
  exists_nonpower_pow u hu

theorem root_length (v : FreeGroup (Fin d)) (k : ℕ) (hv : v ≠ 1) : k ≤ (v ^ k).toWord.length :=
  length_toWord_pow_ge v hv k

theorem wordFree_length (w : List (Letter d)) : (wordFree w).toWord.length ≤ w.length := by
  induction w with
  | nil => simp [wordFree]
  | cons a w ih =>
    have hs : ∃ x : FreeGroup (Fin d), x.toWord.length ≤ 1 ∧ wordFree (a :: w) = x * wordFree w := by
      rcases a with _ | (i | i)
      · exact ⟨1, by simp, by simp [wordFree]⟩
      · exact ⟨FreeGroup.of i, by simp, by simp [wordFree]⟩
      · exact ⟨(FreeGroup.of i)⁻¹, by simp, by simp [wordFree]⟩
    obtain ⟨x, hx, hxe⟩ := hs
    rw [hxe]
    have := FreeGroup.norm_mul_le x (wordFree w)
    simp only [FreeGroup.norm] at this
    simp only [List.length_cons]
    omega

end StrongConv.S9.PartR

end
end
end

section
section
open Polynomial Filter Topology
noncomputable section
open scoped Classical
namespace StrongConv.S9
variable {d : ℕ}
theorem root_exists (u : FreeGroup (Fin d)) (hu : u ≠ 1) :
    ∃ v : FreeGroup (Fin d), ∃ k : ℕ, IsNonPower v ∧ 1 ≤ k ∧ u = v ^ k :=
  PartR.root_exists u hu
theorem root_unique (v v' : FreeGroup (Fin d)) (k k' : ℕ) (hv : IsNonPower v)
    (hv' : IsNonPower v') (hk : 1 ≤ k) (hk' : 1 ≤ k') (h : v ^ k = v' ^ k') : k = k' :=
  PartR.root_unique v v' k k' hv hv' hk hk' h
theorem root_length (v : FreeGroup (Fin d)) (k : ℕ) (hv : v ≠ 1) : k ≤ (v ^ k).toWord.length :=
  PartR.root_length v k hv
theorem wordFree_length (w : List (Letter d)) : (wordFree w).toWord.length ≤ w.length :=
  PartR.wordFree_length w
end StrongConv.S9

end
end
end

section
section
set_option autoImplicit true
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S9

open StrongConv
open scoped Matrix InnerProductSpace

section Part1
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tr_tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    (tensorOp A T x) a = ∑ b, A a b • T (x b) := by
  simp [tensorOp, Pi.single_apply, eq_comm]

theorem tr_star_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    star (tensorOp A T) = tensorOp Aᴴ (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [tr_tensorOp_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  simp [Matrix.conjTranspose_apply]

theorem tr_star_letterOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (l : Fin d ⊕ Fin d) :
    star (letterOp u l) = letterOp u l.swap := by
  rcases l with i | i <;> simp [letterOp]

theorem tr_star_wordOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    star (wordOp u w) = wordOp u (NCPoly.wordStar w) := by
  unfold wordOp NCPoly.wordStar
  induction w.toList using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    simp [star_mul, ih, tr_star_letterOp]

theorem tr_wordStar_involutive {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    NCPoly.wordStar (NCPoly.wordStar w) = w := by
  unfold NCPoly.wordStar
  simp [List.map_reverse, Function.comp_def]

end Part1

/-- `P(u, u*)` is self-adjoint for a self-adjoint `P` and any tuple `u` (the letter `sᵢ*` is
evaluated at `star (u i)`). -/
theorem eval_isSelfAdjoint {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (P.eval u) := by
  have hsupp : ∀ w, NCPoly.wordStar w ∈ P.support ↔ w ∈ P.support := by
    intro w
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff, hP w]
    simp
  let e : FreeMonoid (Fin d ⊕ Fin d) ≃ FreeMonoid (Fin d ⊕ Fin d) :=
    ⟨NCPoly.wordStar, NCPoly.wordStar, tr_wordStar_involutive, tr_wordStar_involutive⟩
  unfold IsSelfAdjoint NCPoly.eval
  have hsum := fun (s : Finset (FreeMonoid (Fin d ⊕ Fin d))) (f : FreeMonoid (Fin d ⊕ Fin d) → (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H))) => star_sum s f
  rw [hsum]
  have : ∑ w ∈ P.support, star (tensorOp (P w) (wordOp u w))
      = ∑ w ∈ P.support, tensorOp (P w) (wordOp u w) := by
    simp_rw [tr_star_tensorOp, tr_star_wordOp]
    refine Finset.sum_equiv e (fun w => (hsupp w).symm) ?_
    intro w hw
    simp only [e, Equiv.coe_fn_mk]
    rw [hP w]
  exact this




section Part2
open scoped ComplexOrder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

end Part2

end StrongConv.S9

end
end
end

section
section
set_option autoImplicit true
open Polynomial Filter Topology

noncomputable section

open scoped Classical

namespace StrongConv.S9.PartLin

open StrongConv StrongConv.S9
open scoped InnerProductSpace

section Tensor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tensorOp_ext {n m : ℕ} (X Y : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H))
    (h : ∀ x a, X x a = Y x a) : X = Y :=
  ContinuousLinearMap.ext fun x => PiLp.ext fun a => h x a

theorem tensorOp_mul {l m n : ℕ} (A : Matrix (Fin l) (Fin m) ℂ) (B : Matrix (Fin m) (Fin n) ℂ)
    (S T : H →L[ℂ] H) :
    (tensorOp A S).comp (tensorOp B T) = tensorOp (A * B) (S.comp T) := by
  refine tensorOp_ext _ _ fun x a => ?_
  simp only [ContinuousLinearMap.comp_apply, tr_tensorOp_apply, map_sum, map_smul,
    Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem tensorOp_add_left {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  refine tensorOp_ext _ _ fun x a => ?_
  simp [tr_tensorOp_apply, add_smul, Finset.sum_add_distrib]

theorem tensorOp_zero_left {m n : ℕ} (T : H →L[ℂ] H) :
    tensorOp (0 : Matrix (Fin m) (Fin n) ℂ) T = 0 := by
  refine tensorOp_ext _ _ fun x a => ?_
  simp [tr_tensorOp_apply]

theorem tensorOp_neg_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (-A) T = - tensorOp A T := by
  refine tensorOp_ext _ _ fun x a => ?_
  simp [tr_tensorOp_apply]

theorem tensorOp_sum_left {ι : Type*} (s : Finset ι) {m n : ℕ} (A : ι → Matrix (Fin m) (Fin n) ℂ)
    (T : H →L[ℂ] H) :
    tensorOp (∑ k ∈ s, A k) T = ∑ k ∈ s, tensorOp (A k) T := by
  induction s using Finset.induction_on with
  | empty => simp [tensorOp_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tensorOp_add_left, ih]

theorem tensorOp_one_one {n : ℕ} : tensorOp (1 : Matrix (Fin n) (Fin n) ℂ) (1 : H →L[ℂ] H) = 1 := by
  refine tensorOp_ext _ _ fun x a => ?_
  simp [tr_tensorOp_apply, Matrix.one_apply]

end Tensor


/-! ## Expansion of the chain for a general tuple -/

variable {d : ℕ}

section Chain
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def XopU (L : Lin d) (u : Fin d → H →L[ℂ] H) (j : ℕ) :
    PiLp 2 (fun _ : Fin L.Dm => H) →L[ℂ] PiLp 2 (fun _ : Fin L.Dm => H) :=
  ∑ l : Letter d, tensorOp (L.B j l) (wordEval u [l])

def XprodU (L : Lin d) (u : Fin d → H →L[ℂ] H) (m : ℕ) :
    PiLp 2 (fun _ : Fin L.Dm => H) →L[ℂ] PiLp 2 (fun _ : Fin L.Dm => H) :=
  ((List.range m).map fun j => XopU L u (j + 1)).prod

theorem Xprod_eq (L : Lin d) (m : ℕ) : Xprod L m = XprodU L (sLimit d) m := rfl

theorem wordEval_append (u : Fin d → H →L[ℂ] H) (w w' : List (Letter d)) :
    wordEval u (w ++ w') = wordEval u w * wordEval u w' := by
  simp [wordEval]

theorem XprodU_succ (L : Lin d) (u : Fin d → H →L[ℂ] H) (m : ℕ) :
    XprodU L u (m + 1) = XprodU L u m * XopU L u (m + 1) := by
  simp [XprodU, List.range_succ]

theorem Bprod_snoc (L : Lin d) (m : ℕ) (i : Fin m → Letter d) (a : Letter d) :
    Bprod L (m + 1) (Fin.snoc i a) = Bprod L m i * L.B (m + 1) a := by
  unfold Bprod
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

theorem ofFn_snoc_eval (u : Fin d → H →L[ℂ] H) (m : ℕ) (i : Fin m → Letter d) (a : Letter d) :
    wordEval u (List.ofFn (Fin.snoc i a : Fin (m + 1) → Letter d)) =
      wordEval u (List.ofFn i) * wordEval u [a] := by
  rw [List.ofFn_succ']
  simp [List.concat_eq_append, wordEval_append]

def snocEquiv (m : ℕ) : (Fin m → Letter d) × Letter d ≃ (Fin (m + 1) → Letter d) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (Fin.init f, f (Fin.last m))
  left_inv p := by simp
  right_inv f := by simp

theorem XprodU_expand (L : Lin d) (u : Fin d → H →L[ℂ] H) (m : ℕ) :
    XprodU L u m = ∑ i : Fin m → Letter d,
      tensorOp (Bprod L m i) (wordEval u (List.ofFn i)) := by
  induction m with
  | zero =>
    simp [XprodU, Bprod, tensorOp_one_one, wordEval]
  | succ m ih =>
    rw [XprodU_succ, ih, XopU, Finset.sum_mul]
    rw [← Fintype.sum_equiv (snocEquiv m) (fun p => tensorOp (Bprod L (m + 1) (snocEquiv m p))
        (wordEval u (List.ofFn (snocEquiv m p)))) _ (fun p => rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [snocEquiv, Equiv.coe_fn_mk, Bprod_snoc, ofFn_snoc_eval]
    exact tensorOp_mul _ _ _ _

theorem XopU_add_q (L : Lin d) (u : Fin d → H →L[ℂ] H) (j : ℕ) :
    XopU L u (j + L.q) = XopU L u j := by
  simp [XopU, L.periodic]

theorem XopU_add_mul (L : Lin d) (u : Fin d → H →L[ℂ] H) (j k : ℕ) :
    XopU L u (j + k * L.q) = XopU L u j := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul, ← add_assoc, XopU_add_q, ih]

theorem XprodU_add (L : Lin d) (u : Fin d → H →L[ℂ] H) (a b : ℕ) :
    XprodU L u (a + b) = XprodU L u a *
      ((List.range b).map fun j => XopU L u (a + j + 1)).prod := by
  simp only [XprodU, List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 3

theorem XprodU_mul_q (L : Lin d) (u : Fin d → H →L[ℂ] H) (p : ℕ) :
    XprodU L u (p * L.q) = XprodU L u L.q ^ p := by
  induction p with
  | zero => simp [XprodU]
  | succ p ih =>
    rw [Nat.succ_mul, XprodU_add, ih, pow_succ]
    congr 1
    simp only [XprodU]
    congr 1
    apply List.map_congr_left
    intro j _
    have := XopU_add_mul L u (j + 1) p
    rw [← this]
    congr 1
    ring

end Chain

/-! ## Padding by zeros -/

/-- The zero-padding (or truncation) matrix. -/
def Emat (n m : ℕ) : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun x y => if (x : ℕ) = y then 1 else 0

theorem Emat_mul {a b c : ℕ} (h : a ≤ b) : Emat b c * Emat a b = Emat a c := by
  ext x y
  simp only [Matrix.mul_apply, Emat, Matrix.of_apply]
  rw [Finset.sum_eq_single (⟨y, lt_of_lt_of_le y.2 h⟩ : Fin b)]
  · simp
  · intro z _ hz
    have : (z : ℕ) ≠ y := fun h' => hz (Fin.ext h')
    simp [this]
  · simp

theorem Emat_self (n : ℕ) : Emat n n = 1 := by
  ext x y
  simp [Emat, Matrix.one_apply, Fin.ext_iff]

section Pad
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Embedding of `n` copies into `m` copies by padding with zeros (or truncation). -/
def padOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (n m : ℕ) : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H) :=
  tensorOp (Emat n m) (1 : H →L[ℂ] H)

theorem padOp_apply (n m : ℕ) (x : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    padOp H n m x a = if h : (a : ℕ) < n then x ⟨a, h⟩ else 0 := by
  rw [padOp, tr_tensorOp_apply]
  by_cases h : (a : ℕ) < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨a, h⟩ : Fin n)]
    · simp [Emat]
    · intro b _ hb
      have : (a : ℕ) ≠ b := fun h' => hb (Fin.ext h'.symm)
      simp [Emat, this]
    · simp
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : (a : ℕ) ≠ b := fun h' => h (h' ▸ b.2)
    simp [Emat, this]

theorem padOp_norm_le (n m : ℕ) (x : PiLp 2 (fun _ : Fin n => H)) : ‖padOp H n m x‖ ≤ ‖x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  set g : ℕ → ℝ := fun k => if h : k < n then ‖x ⟨k, h⟩‖ ^ 2 else 0 with hg
  have h1 : ∑ a : Fin m, ‖padOp H n m x a‖ ^ 2 = ∑ k ∈ Finset.range m, g k := by
    rw [← Fin.sum_univ_eq_sum_range g m]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [padOp_apply]
    by_cases h : (a : ℕ) < n <;> simp [hg, h]
  have h2 : ∑ b : Fin n, ‖x b‖ ^ 2 = ∑ k ∈ Finset.range n, g k := by
    rw [← Fin.sum_univ_eq_sum_range g n]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [hg]
  rw [h1, h2]
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    by_cases h : k < n <;> simp [hg, h]
  calc ∑ k ∈ Finset.range m, g k = ∑ k ∈ Finset.range m ∩ Finset.range n, g k := by
        symm
        refine Finset.sum_subset Finset.inter_subset_left fun k hk hk' => ?_
        have : ¬ k < n := fun h => hk' (Finset.mem_inter.mpr ⟨hk, Finset.mem_range.mpr h⟩)
        simp [hg, this]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun k _ _ => hg0 k)

theorem padOp_opNorm_le (n m : ℕ) : ‖padOp H n m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simpa using padOp_norm_le n m x

theorem padOp_comp (n m : ℕ) (h : n ≤ m) : (padOp H m n).comp (padOp H n m) = 1 := by
  unfold padOp
  rw [tensorOp_mul, Emat_mul h, Emat_self, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ← ContinuousLinearMap.one_def, tensorOp_one_one]

end Pad


/-! ## The padded linearization -/

theorem linOp_conj {a b c e : ℕ} (E1 : Matrix (Fin c) (Fin a) ℂ) (E2 : Matrix (Fin b) (Fin e) ℂ)
    (A : Letter d → Matrix (Fin a) (Fin b) ℂ) :
    linOp (fun l => E1 * A l * E2) =
      (tensorOp E1 (1 : L2Free d →L[ℂ] L2Free d)).comp
        ((linOp A).comp (tensorOp E2 (1 : L2Free d →L[ℂ] L2Free d))) := by
  ext x : 1
  simp only [linOp, ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have key : tensorOp (E1 * A l * E2) (wordEval (sLimit d) [l]) =
      (tensorOp E1 (1 : L2Free d →L[ℂ] L2Free d)).comp
        ((tensorOp (A l) (wordEval (sLimit d) [l])).comp
          (tensorOp E2 (1 : L2Free d →L[ℂ] L2Free d))) := by
    rw [tensorOp_mul, tensorOp_mul, Matrix.mul_assoc]
    congr 1
  rw [key]
  rfl

def jj (q j : ℕ) : ℕ := (j + q - 1) % q + 1

theorem jj_add (q : ℕ) (hq : 1 ≤ q) (j : ℕ) : jj q (j + q) = jj q j := by
  unfold jj
  have : j + q + q - 1 = (j + q - 1) + q := by omega
  rw [this, Nat.add_mod_right]

theorem jj_mem (q : ℕ) (hq : 1 ≤ q) (j : ℕ) : 1 ≤ jj q j ∧ jj q j ≤ q := by
  unfold jj
  have := Nat.mod_lt (j + q - 1) hq
  omega

theorem jj_self (q : ℕ) (hq : 1 ≤ q) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ q) : jj q j = j := by
  unfold jj
  have : j + q - 1 = (j - 1) + q := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

def DmOf (q : ℕ) (Dim : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range (q + 2), Dim j

theorem Dim_le_DmOf (q : ℕ) (Dim : ℕ → ℕ) (a : ℕ) (h : a ≤ q + 1) : Dim a ≤ DmOf q Dim :=
  Finset.single_le_sum (f := Dim) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (by omega))

/-- The padded block `E A_k E'`. -/
def Bf (q : ℕ) (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) (k : ℕ) (l : Letter d) :
    Matrix (Fin (DmOf q Dim)) (Fin (DmOf q Dim)) ℂ :=
  Emat (Dim k) (DmOf q Dim) * A k l * Emat (DmOf q Dim) (Dim (k + 1))

def mkLin (q : ℕ) (hq : 1 ≤ q) (Dim : ℕ → ℕ)
    (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ) : Lin d where
  q := q
  hq := hq
  Dm := DmOf q Dim
  B := fun j l => Bf q Dim A (jj q j) l
  periodic := by
    intro j l
    show Bf q Dim A (jj q (j + q)) l = Bf q Dim A (jj q j) l
    rw [jj_add q hq]

section MkLin
variable (q : ℕ) (hq : 1 ≤ q) (Dim : ℕ → ℕ)
  (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)

theorem Xop_pad_of (j k : ℕ) (hjk : jj q j = k) :
    Xop (mkLin q hq Dim A) j =
      (padOp (L2Free d) (Dim k) (DmOf q Dim)).comp
        ((linOp (A k)).comp (padOp (L2Free d) (DmOf q Dim) (Dim (k + 1)))) := by
  subst hjk
  exact linOp_conj (Emat (Dim (jj q j)) (DmOf q Dim)) (Emat (DmOf q Dim) (Dim (jj q j + 1)))
    (A (jj q j))

theorem Xop_norm_le (R : ℝ)
    (hA : ∀ j ∈ Finset.Icc 1 q, ‖linOp (A j)‖ ≤ R) (j : ℕ) :
    ‖Xop (mkLin q hq Dim A) j‖ ≤ R := by
  have hj := jj_mem q hq j
  rw [Xop_pad_of q hq Dim A j (jj q j) rfl]
  calc _ ≤ ‖padOp (L2Free d) (Dim (jj q j)) (DmOf q Dim)‖ *
        (‖linOp (A (jj q j))‖ * ‖padOp (L2Free d) (DmOf q Dim) (Dim (jj q j + 1))‖) := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (R * 1) := by
        have h1 := padOp_opNorm_le (H := L2Free d) (Dim (jj q j)) (DmOf q Dim)
        have h2 := padOp_opNorm_le (H := L2Free d) (DmOf q Dim) (Dim (jj q j + 1))
        have h3 := hA (jj q j) (Finset.mem_Icc.mpr hj)
        have hR : 0 ≤ R := (norm_nonneg _).trans h3
        gcongr
    _ = R := by ring

theorem Xprod_pad : ∀ m : ℕ, 1 ≤ m → m ≤ q →
    Xprod (mkLin q hq Dim A) m =
      (padOp (L2Free d) (Dim 1) (DmOf q Dim)).comp
        ((linChain Dim A 1 m).comp (padOp (L2Free d) (DmOf q Dim) (Dim (1 + m)))) := by
  intro m hm1
  induction m, hm1 using Nat.le_induction with
  | base =>
    intro hmq
    have : Xprod (mkLin q hq Dim A) 1 = Xop (mkLin q hq Dim A) 1 := by simp [Xprod]
    rw [this, Xop_pad_of q hq Dim A 1 1 (jj_self q hq 1 le_rfl hmq)]
    rfl
  | succ m hm ih =>
    intro hmq
    have hs : Xprod (mkLin q hq Dim A) (m + 1) =
        Xprod (mkLin q hq Dim A) m * Xop (mkLin q hq Dim A) (m + 1) := by
      simp [Xprod, List.range_succ]
    have hj : jj q (m + 1) = 1 + m := by
      rw [jj_self q hq (m + 1) (by omega) hmq]; omega
    rw [hs, Xop_pad_of q hq Dim A (m + 1) (1 + m) hj, ih (by omega)]
    have hc := padOp_comp (H := L2Free d) (Dim (1 + m)) (DmOf q Dim)
      (Dim_le_DmOf q Dim (1 + m) (by omega))
    have key : ((padOp (L2Free d) (Dim 1) (DmOf q Dim)).comp
        ((linChain Dim A 1 m).comp (padOp (L2Free d) (DmOf q Dim) (Dim (1 + m))))).comp
        ((padOp (L2Free d) (Dim (1 + m)) (DmOf q Dim)).comp
          ((linOp (A (1 + m))).comp (padOp (L2Free d) (DmOf q Dim) (Dim (1 + m + 1))))) =
        (padOp (L2Free d) (Dim 1) (DmOf q Dim)).comp
        ((linChain Dim A 1 (m + 1)).comp
          (padOp (L2Free d) (DmOf q Dim) (Dim (1 + (m + 1))))) := by
      ext x : 1
      simp only [ContinuousLinearMap.comp_apply]
      have := congrArg (fun f => f (linOp (A (1 + m)) (padOp (L2Free d) (DmOf q Dim)
        (Dim (1 + m + 1)) x))) hc
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
      rw [this]
      rfl
    exact key

end MkLin


/-! ## Trace of a tensor operator -/

section Trace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

theorem trace_tensorOp_term {n : ℕ} (a b : Fin n) (T : H →L[ℂ] H) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin n => H))
      (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.single ℂ (fun _ : Fin n => H) a).comp
          (T.comp (PiLp.proj 2 (fun _ : Fin n => H) b))) :
        PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :
        PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H)) =
      if a = b then LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) else 0 := by
  set S : H →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H) :=
    (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) a) :
        H →L[ℂ] PiLp 2 (fun _ : Fin n => H)) : H →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H)) with hS
  set F : PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] H :=
    ((T.comp (PiLp.proj 2 (fun _ : Fin n => H) b) : PiLp 2 (fun _ : Fin n => H) →L[ℂ] H) :
      PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] H) with hF
  have h1 : (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
        ((ContinuousLinearMap.single ℂ (fun _ : Fin n => H) a).comp
          (T.comp (PiLp.proj 2 (fun _ : Fin n => H) b))) :
        PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :
        PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H)) = S ∘ₗ F := by
    ext x : 1
    simp [hS, hF]
  rw [h1, LinearMap.trace_comp_comm' F S]
  by_cases hab : a = b
  · subst hab
    have : F ∘ₗ S = (T : H →ₗ[ℂ] H) := by
      ext y : 1
      simp [hS, hF]
    rw [this, if_pos rfl]
  · have : F ∘ₗ S = 0 := by
      ext y : 1
      simp [hS, hF, Pi.single_apply, hab, Ne.symm hab]
    rw [this, if_neg hab, map_zero]

theorem trace_tensorOp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (T : H →L[ℂ] H) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin n => H))
      ((tensorOp A T : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H)) :
        PiLp 2 (fun _ : Fin n => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H)) =
      A.trace * LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) := by
  unfold tensorOp
  simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul, map_sum, map_smul,
    trace_tensorOp_term, smul_eq_mul]
  simp [Matrix.trace, Finset.sum_mul, mul_ite, Finset.sum_ite_eq]

end Trace


/-! ## Compression to the top-left block -/

section Compress
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (L : Lin d) (D : ℕ) (hDm : D ≤ L.Dm) (hS1 : ∀ l (a b : Fin L.Dm), D ≤ (a : ℕ) → L.B 1 l a b = 0)
  (u : Fin d → H →L[ℂ] H)

include hS1 in
theorem XopU_one_zero (x : PiLp 2 (fun _ : Fin L.Dm => H)) (a : Fin L.Dm) (ha : D ≤ (a : ℕ)) :
    XopU L u 1 x a = 0 := by
  simp [XopU, tr_tensorOp_apply, hS1 _ a _ ha]

include hS1 in
theorem XprodU_zero : ∀ m : ℕ, 1 ≤ m → ∀ (x : PiLp 2 (fun _ : Fin L.Dm => H)) (a : Fin L.Dm),
    D ≤ (a : ℕ) → XprodU L u m x a = 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro x a ha
    have : XprodU L u 1 = XopU L u 1 := by simp [XprodU]
    rw [this]
    exact XopU_one_zero L D hS1 u x a ha
  | succ m hm ih =>
    intro x a ha
    rw [XprodU_succ]
    exact ih _ a ha

include hDm in
theorem pad_absorb (z : PiLp 2 (fun _ : Fin L.Dm => H)) (hz : ∀ a : Fin L.Dm, D ≤ (a : ℕ) → z a = 0) :
    padOp H D L.Dm (padOp H L.Dm D z) = z := by
  refine PiLp.ext fun a => ?_
  rw [padOp_apply]
  by_cases h : (a : ℕ) < D
  · rw [dif_pos h, padOp_apply, dif_pos (lt_of_lt_of_le h hDm)]
  · rw [dif_neg h, hz a (not_lt.mp h)]

include hS1 hDm in
theorem compress_absorb (m : ℕ) (hm : 1 ≤ m) (x : PiLp 2 (fun _ : Fin L.Dm => H)) :
    padOp H D L.Dm (padOp H L.Dm D (XprodU L u m x)) = XprodU L u m x :=
  pad_absorb L D hDm _ (XprodU_zero L D hS1 u m hm x)

/-- The compression of `X_1 ⋯ X_q` to the top-left `D × D` block. -/
def Tcomp : PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H) :=
  (padOp H L.Dm D).comp ((XprodU L u L.q).comp (padOp H D L.Dm))

include hS1 hDm in
theorem Tcomp_pow (hq : 1 ≤ L.q) : ∀ p : ℕ, 1 ≤ p →
    Tcomp L D u ^ p = (padOp H L.Dm D).comp ((XprodU L u L.q ^ p).comp (padOp H D L.Dm)) := by
  intro p hp
  induction p, hp using Nat.le_induction with
  | base => simp [Tcomp]
  | succ p hp ih =>
    rw [pow_succ, ih]
    ext x : 1
    simp only [Tcomp, ContinuousLinearMap.comp_apply, mul_apply_eq_comp, pow_succ]
    rw [compress_absorb L D hDm hS1 u L.q hq]

end Compress

section TraceCompress
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]
  (L : Lin d) (D : ℕ) (hDm : D ≤ L.Dm) (hS1 : ∀ l (a b : Fin L.Dm), D ≤ (a : ℕ) → L.B 1 l a b = 0)
  (u : Fin d → H →L[ℂ] H)

include hS1 hDm in
theorem trace_Tcomp_pow (hq : 1 ≤ L.q) (p : ℕ) (hp : 1 ≤ p) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => H))
      ((Tcomp L D u ^ p : PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) :
        PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H)) =
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin L.Dm => H))
      ((XprodU L u (p * L.q) : PiLp 2 (fun _ : Fin L.Dm => H) →L[ℂ] PiLp 2 (fun _ : Fin L.Dm => H)) :
        PiLp 2 (fun _ : Fin L.Dm => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin L.Dm => H)) := by
  rw [Tcomp_pow L D hDm hS1 u hq p hp]
  set ι : PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin L.Dm => H) :=
    ((padOp H D L.Dm : PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin L.Dm => H)) :
      PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin L.Dm => H)) with hι
  set g : PiLp 2 (fun _ : Fin L.Dm => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H) :=
    (((padOp H L.Dm D).comp (XprodU L u L.q ^ p) : PiLp 2 (fun _ : Fin L.Dm => H) →L[ℂ] _) :
      PiLp 2 (fun _ : Fin L.Dm => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H)) with hg
  have h1 : (((padOp H L.Dm D).comp ((XprodU L u L.q ^ p).comp (padOp H D L.Dm)) :
      PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) :
      PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H)) = g ∘ₗ ι := by
    ext x : 1
    simp [hg, hι]
  rw [h1, LinearMap.trace_comp_comm' ι g]
  congr 1
  rw [XprodU_mul_q]
  ext x : 1
  have hm : 1 ≤ p * L.q := Nat.mul_pos hp hq
  have := compress_absorb L D hDm hS1 u (p * L.q) hm x
  rw [XprodU_mul_q] at this
  exact this

theorem trace_XprodU (m : ℕ) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin L.Dm => H))
      ((XprodU L u m : PiLp 2 (fun _ : Fin L.Dm => H) →L[ℂ] PiLp 2 (fun _ : Fin L.Dm => H)) :
        PiLp 2 (fun _ : Fin L.Dm => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin L.Dm => H)) =
    ∑ i : Fin m → Letter d, (Bprod L m i).trace *
      LinearMap.trace ℂ H ((wordEval u (List.ofFn i) : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  rw [XprodU_expand]
  simp only [ContinuousLinearMap.toLinearMap_sum, map_sum, trace_tensorOp]

end TraceCompress


/-! ## Transfer: from the free group to permutation models -/

section Transfer
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tensorOp_sub_left {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A - B) T = tensorOp A T - tensorOp B T := by
  rw [sub_eq_add_neg, tensorOp_add_left, tensorOp_neg_left, sub_eq_add_neg]

theorem tensorOp_conj {a b c e : ℕ} (E1 : Matrix (Fin c) (Fin a) ℂ) (E2 : Matrix (Fin b) (Fin e) ℂ)
    (C : Matrix (Fin a) (Fin b) ℂ) (W : H →L[ℂ] H) :
    (tensorOp E1 (1 : H →L[ℂ] H)).comp ((tensorOp C W).comp (tensorOp E2 (1 : H →L[ℂ] H))) =
      tensorOp (E1 * C * E2) W := by
  rw [tensorOp_mul, tensorOp_mul, Matrix.mul_assoc]
  congr 1

/-- The word `w ∈ FreeMonoid` as a list of letters. -/
def wl (w : FreeMonoid (Fin d ⊕ Fin d)) : List (Letter d) := w.toList.map some

theorem wordOp_eq (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp u w = wordEval u (wl w) := by
  unfold wordOp wordEval wl
  simp [List.map_map, Function.comp_def]

theorem eval_expand {D : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    P.eval u = ∑ w ∈ P.support, tensorOp (P w) (wordEval u (wl w)) := by
  unfold NCPoly.eval
  simp only [wordOp_eq]

/-- The compression of a matrix to the top-left `D × D` block. -/
def blk (Dm D : ℕ) (C : Matrix (Fin Dm) (Fin Dm) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Emat Dm D * C * Emat D Dm

theorem Tcomp_expand (L : Lin d) (D : ℕ) (u : Fin d → H →L[ℂ] H) :
    Tcomp L D u = ∑ i : Fin L.q → Letter d,
      tensorOp (blk L.Dm D (Bprod L L.q i)) (wordEval u (List.ofFn i)) := by
  unfold Tcomp
  rw [XprodU_expand]
  ext x : 1
  simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := tensorOp_conj (Emat L.Dm D) (Emat D L.Dm) (Bprod L L.q i) (wordEval u (List.ofFn i))
  rw [blk, ← this]
  rfl

/-- Grouping a finite sum by the value of the free-group element. -/
theorem sum_fiber {ι : Type*} {m n : ℕ} (s : Finset ι) (t : Finset (FreeGroup (Fin d)))
    (g : ι → FreeGroup (Fin d)) (hg : ∀ i ∈ s, g i ∈ t) (Mt : ι → Matrix (Fin m) (Fin n) ℂ)
    (Pi : FreeGroup (Fin d) → (H →L[ℂ] H)) :
    ∑ i ∈ s, tensorOp (Mt i) (Pi (g i)) =
      ∑ h ∈ t, tensorOp (∑ i ∈ s with g i = h, Mt i) (Pi h) := by
  rw [← Finset.sum_fiberwise_of_maps_to hg]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [tensorOp_sum_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

end Transfer

/-! ## Copies from Solutions/StrongConvS5 -/

/-! ### The left-regular representation -/

lemma leftReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    leftReg g f h = f (g⁻¹ * h) := rfl

lemma leftReg_mul {d : ℕ} (g g' : FreeGroup (Fin d)) :
    leftReg (g * g') = leftReg g * leftReg g' := by
  ext f h
  simp only [leftReg_apply, mul_apply_eq_comp, mul_inv_rev, mul_assoc]

lemma leftReg_one {d : ℕ} : leftReg (1 : FreeGroup (Fin d)) = 1 := by
  ext f h
  simp [leftReg_apply]

lemma star_leftReg {d : ℕ} (g : FreeGroup (Fin d)) : star (leftReg g) = leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

lemma wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    wordEval (sLimit d) w = leftReg (wordFree w) := by
  induction w with
  | nil => simp [wordEval, wordFree, leftReg_one]
  | cons a w ih =>
    simp only [wordEval, wordFree, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, leftReg_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [leftReg_one]
    · simp [letterOp, sLimit]
    · simp [letterOp, sLimit, star_leftReg]



/-! ## Coefficient extraction in the regular representation -/

theorem leftReg_delta_one {d : ℕ} (g h : FreeGroup (Fin d)) :
    leftReg g (delta 1) h = if g = h then 1 else 0 := by
  rw [leftReg_apply, delta, lp.single_apply]
  by_cases hgh : g = h
  · subst hgh; simp
  · rw [if_neg hgh]
    simp only [Pi.single_apply]
    rw [if_neg]
    intro h'
    apply hgh
    have : g⁻¹ * h = 1 := h'
    exact inv_injective (mul_eq_one_iff_eq_inv.mp this)

theorem extract {D : ℕ} (S : Finset (FreeGroup (Fin d)))
    (C : FreeGroup (Fin d) → Matrix (Fin D) (Fin D) ℂ)
    (h : ∑ g ∈ S, tensorOp (C g) (leftReg g) = 0) : ∀ g ∈ S, C g = 0 := by
  intro g0 hg0
  ext x y
  have h1 := congrArg (fun T => (T (PiLp.single 2 y (delta (1 : FreeGroup (Fin d))) :
    PiLp 2 (fun _ : Fin D => L2Free d))) x) h
  simp only [sum_apply, ContinuousLinearMap.zero_apply] at h1
  simp [tr_tensorOp_apply, PiLp.single_apply, apply_ite (leftReg _), smul_ite,
    Finset.sum_ite_eq'] at h1
  have h2 := congrArg (fun f : L2Free d => f g0) h1
  rw [lp.coeFn_sum, Finset.sum_apply] at h2
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at h2
  simp [leftReg_delta_one, Finset.sum_ite_eq, hg0] at h2
  simpa using h2


/-! ## The transfer principle -/

section Transfer2
variable {D : ℕ} (P : NCPoly D d) (L : Lin d)

def tIdx : Finset (FreeGroup (Fin d)) :=
  P.support.image (fun w => wordFree (wl w)) ∪
    (Finset.univ : Finset (Fin L.q → Letter d)).image (fun i => wordFree (List.ofFn i))

def CP (h : FreeGroup (Fin d)) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ w ∈ P.support with wordFree (wl w) = h, P w

def CB (h : FreeGroup (Fin d)) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ i ∈ (Finset.univ : Finset (Fin L.q → Letter d)) with wordFree (List.ofFn i) = h,
    blk L.Dm D (Bprod L L.q i)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem eval_expand_fiber (u : Fin d → H →L[ℂ] H) (Pi : FreeGroup (Fin d) → (H →L[ℂ] H))
    (hPi : ∀ w, wordEval u w = Pi (wordFree w)) :
    P.eval u = ∑ h ∈ tIdx P L, tensorOp (CP P h) (Pi h) := by
  rw [eval_expand]
  simp_rw [hPi]
  rw [sum_fiber P.support (tIdx P L) (fun w => wordFree (wl w))
    (fun w hw => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw))]
  rfl

theorem Tcomp_expand_fiber (u : Fin d → H →L[ℂ] H) (Pi : FreeGroup (Fin d) → (H →L[ℂ] H))
    (hPi : ∀ w, wordEval u w = Pi (wordFree w)) :
    Tcomp L D u = ∑ h ∈ tIdx P L, tensorOp (CB L h) (Pi h) := by
  rw [Tcomp_expand]
  simp_rw [hPi]
  rw [sum_fiber Finset.univ (tIdx P L) (fun i => wordFree (List.ofFn i))
    (fun i hi => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hi))]
  rfl

end Transfer2


/-! ## Functional calculus of a power -/

theorem fnCalc_pow {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →L[ℂ] V) (hT : IsSelfAdjoint T) (p : ℕ) :
    fnCalc (fun x => x ^ p) T = T ^ p := by
  unfold fnCalc
  have h : cfc (fun z : ℂ => (((z.re) ^ p : ℝ) : ℂ)) T = cfc (fun z : ℂ => z ^ p) T := by
    refine cfc_congr fun z hz => ?_
    have := hT.mem_spectrum_eq_re hz
    push_cast
    conv_rhs => rw [this]
  haveI := hT.isStarNormal
  rw [h, cfc_pow_id T p]

/-! ## Padding and `linChainOn` -/

section PadReindex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem padOp_comp2 {n m k : ℕ} (h : n ≤ m) :
    (padOp H m k).comp (padOp H n m) = padOp H n k := by
  unfold padOp
  rw [tensorOp_mul, Emat_mul h]
  congr 1

theorem padOp_reindex {n k : ℕ} (h : n = k) : padOp H n k = reindexCopies (finCongr h) := by
  subst h
  unfold padOp reindexCopies
  rw [Emat_self, tensorOp_one_one]
  ext x i
  simp

end PadReindex


/-! ## Support and the identity at the free group -/

section MkLin2
variable (q : ℕ) (hq : 1 ≤ q) (Dim : ℕ → ℕ)
  (A : ∀ j : ℕ, Letter d → Matrix (Fin (Dim j)) (Fin (Dim (j + 1))) ℂ)

theorem mkLin_supp1 (D : ℕ) (h1 : Dim 1 = D) (l : Letter d) (a b : Fin (DmOf q Dim))
    (ha : D ≤ (a : ℕ)) : (mkLin q hq Dim A).B 1 l a b = 0 := by
  show Bf q Dim A (jj q 1) l a b = 0
  rw [jj_self q hq 1 le_rfl hq]
  simp only [Bf, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Finset.sum_eq_zero, zero_mul]
  intro x _
  have : (a : ℕ) ≠ x := by have := x.2; omega
  simp [Emat, this]

theorem mkLin_supp2 (D : ℕ) (hq' : Dim (1 + q) = D) (l : Letter d) (a b : Fin (DmOf q Dim))
    (hb : D ≤ (b : ℕ)) : (mkLin q hq Dim A).B q l a b = 0 := by
  show Bf q Dim A (jj q q) l a b = 0
  rw [jj_self q hq q hq le_rfl]
  simp only [Bf, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  have : (y : ℕ) ≠ b := by
    have := y.2
    have h2 : Dim (q + 1) = D := by rw [Nat.add_comm]; exact hq'
    omega
  simp [Emat, this]

theorem hlim_of {D : ℕ} (P : NCPoly D d) (h1 : Dim 1 = D) (hq' : Dim (1 + q) = D)
    (heq : P.eval (sLimit d) = linChainOn Dim A q h1 hq') :
    P.eval (sLimit d) = Tcomp (mkLin q hq Dim A) D (sLimit d) := by
  have hD : D ≤ DmOf q Dim := h1 ▸ Dim_le_DmOf q Dim 1 (by omega)
  have hD1 : Dim 1 ≤ DmOf q Dim := Dim_le_DmOf q Dim 1 (by omega)
  have hX := Xprod_pad q hq Dim A q hq le_rfl
  have e1 := padOp_comp2 (H := L2Free d) (k := D) hD1
  have e2 := padOp_comp2 (H := L2Free d) (k := Dim (1 + q)) hD
  rw [padOp_reindex h1] at e1
  rw [padOp_reindex hq'.symm] at e2
  have key : linChainOn Dim A q h1 hq' =
      (padOp (L2Free d) (DmOf q Dim) D).comp
        (((padOp (L2Free d) (Dim 1) (DmOf q Dim)).comp
          ((linChain Dim A 1 q).comp (padOp (L2Free d) (DmOf q Dim) (Dim (1 + q))))).comp
          (padOp (L2Free d) D (DmOf q Dim))) := by
    unfold linChainOn
    ext x : 1
    have h3 := congrArg (fun f => f (linChain Dim A 1 q
      (padOp (L2Free d) (DmOf q Dim) (Dim (1 + q)) (padOp (L2Free d) D (DmOf q Dim) x)))) e1
    have h4 := congrArg (fun f => f x) e2
    simp only [ContinuousLinearMap.comp_apply] at h3 h4 ⊢
    rw [h3, h4]
    simp
  rw [heq]
  refine key.trans ?_
  unfold Tcomp
  exact congrArg (fun Y => (padOp (L2Free d) (DmOf q Dim) D).comp
    (Y.comp (padOp (L2Free d) D (DmOf q Dim)))) hX.symm

end MkLin2

end StrongConv.S9.PartLin

end
end
end

section
section
set_option autoImplicit true
open Polynomial Filter Topology

noncomputable section

open scoped Classical

namespace StrongConv.S9.PartLim

open StrongConv StrongConv.S9

/-! ### Copied from S5 PartPerm -/

open scoped InnerProductSpace

/-! ### The left-regular representation -/


/-! ### The pieces -/

end StrongConv.S9.PartLim

end
end
end

section
section
set_option autoImplicit true
open Polynomial Filter Topology

noncomputable section

open scoped Classical

namespace StrongConv.S9.PartCore

open StrongConv StrongConv.S9

variable {d : ℕ}

/-! ### Words and the free group -/

def gl (a : Letter d) : FreeGroup (Fin d) := wordFree [a]

lemma wordFree_nil : wordFree ([] : List (Letter d)) = 1 := by simp [wordFree]

lemma wordFree_cons (a : Letter d) (w : List (Letter d)) :
    wordFree (a :: w) = gl a * wordFree w := by simp [wordFree, gl]

lemma wordFree_append (w w' : List (Letter d)) :
    wordFree (w ++ w') = wordFree w * wordFree w' := by simp [wordFree]

lemma gl_cases (a : Letter d) : gl a = 1 ∨ ∃ p : Fin d × Bool, gl a = FreeGroup.mk [p] := by
  rcases a with _ | (i | i)
  · left; simp [gl, wordFree]
  · right; exact ⟨(i, true), by simp [gl, wordFree, FreeGroup.of]⟩
  · right
    refine ⟨(i, false), ?_⟩
    simp [gl, wordFree, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

lemma toWord_gl_mul (a : Letter d) (T : FreeGroup (Fin d)) :
    (gl a * T).toWord <:+ T.toWord ∨ ∃ p, (gl a * T).toWord = p :: T.toWord := by
  rcases gl_cases a with h | ⟨p, hp⟩
  · rw [h, one_mul]; left; exact List.suffix_refl _
  · rw [hp, FreeGroup.toWord_mul, FreeGroup.toWord_mk, FreeGroup.reduce_singleton]
    simp only [List.singleton_append, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
    rcases hR : T.toWord with _ | ⟨hd, tl⟩
    · right; exact ⟨p, rfl⟩
    · simp only
      split_ifs
      · left; exact List.suffix_cons _ _
      · right; exact ⟨p, rfl⟩

theorem walk_hit (v : FreeGroup (Fin d)) : ∀ w : List (Letter d),
    v.toWord <:+ (wordFree w).toWord → ∃ l, l ≤ w.length ∧ wordFree (w.drop l) = v := by
  intro w
  induction w with
  | nil =>
    intro h
    refine ⟨0, le_rfl, ?_⟩
    rw [wordFree_nil, FreeGroup.toWord_one] at h
    have := List.eq_nil_of_suffix_nil h
    simpa [wordFree_nil] using (FreeGroup.toWord_eq_nil_iff.mp this).symm
  | cons a w ih =>
    intro h
    by_cases hs : v.toWord <:+ (wordFree w).toWord
    · obtain ⟨l, hl, hv⟩ := ih hs
      exact ⟨l + 1, by simp; omega, by simpa using hv⟩
    · refine ⟨0, by simp, ?_⟩
      rw [wordFree_cons] at h
      rcases toWord_gl_mul a (wordFree w) with h1 | ⟨p, hp⟩
      · exact absurd (h.trans h1) hs
      · rw [hp] at h
        rcases List.suffix_cons_iff.mp h with h2 | h2
        · simp only [List.drop_zero, wordFree_cons]
          apply FreeGroup.toWord_injective
          rw [h2, hp]
        · exact absurd h2 hs

/-! ### Block sums `Om` -/

variable (L : Lin d)

abbrev Mt := Matrix (Fin L.Dm) (Fin L.Dm) ℂ

def Om : ℕ → ℕ → (List (Letter d) → ℂ) → Mt L
  | _, 0, φ => φ [] • (1 : Mt L)
  | t, n + 1, φ => ∑ a : Letter d, L.B t a * Om (t + 1) n (fun w => φ (a :: w))

theorem Om_congr : ∀ (n t : ℕ) (φ ψ : List (Letter d) → ℂ),
    (∀ w, w.length = n → φ w = ψ w) → Om L t n φ = Om L t n ψ
  | 0, t, φ, ψ, h => by simp [Om, h [] rfl]
  | n + 1, t, φ, ψ, h => by
    simp only [Om]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Om_congr n (t + 1) _ (fun w => ψ (a :: w)) (fun w hw => h _ (by simp [hw]))]

theorem Om_add : ∀ (n t : ℕ) (φ ψ : List (Letter d) → ℂ),
    Om L t n (fun w => φ w + ψ w) = Om L t n φ + Om L t n ψ
  | 0, t, φ, ψ => by simp [Om, add_smul]
  | n + 1, t, φ, ψ => by
    simp only [Om]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Om_add n (t + 1) (fun w => φ (a :: w)) (fun w => ψ (a :: w)), mul_add]

theorem Om_smul (c : ℂ) : ∀ (n t : ℕ) (φ : List (Letter d) → ℂ),
    Om L t n (fun w => c * φ w) = c • Om L t n φ
  | 0, t, φ => by simp [Om, smul_smul]
  | n + 1, t, φ => by
    simp only [Om]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Om_smul c n (t + 1) (fun w => φ (a :: w)), mul_smul_comm]

theorem Om_zero : ∀ (n t : ℕ), Om L t n (fun _ => (0 : ℂ)) = 0
  | 0, t => by simp [Om]
  | n + 1, t => by simp [Om, Om_zero n]

theorem Om_sum {ι : Type*} (s : Finset ι) (n t : ℕ) (φ : ι → List (Letter d) → ℂ) :
    Om L t n (fun w => ∑ i ∈ s, φ i w) = ∑ i ∈ s, Om L t n (φ i) := by
  induction s using Finset.induction_on with
  | empty => simpa using Om_zero L n t
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Om_add L n t (φ a) (fun w => ∑ i ∈ s, φ i w), ih]

theorem Om_split (φ1 φ2 : List (Letter d) → ℂ) : ∀ (a t b : ℕ),
    Om L t (a + b) (fun w => φ1 (w.take a) * φ2 (w.drop a)) = Om L t a φ1 * Om L (t + a) b φ2 := by
  intro a
  induction a generalizing φ1 with
  | zero =>
    intro t b
    have := Om_smul L (φ1 []) b t φ2
    simp only [Om, List.take_zero, List.drop_zero, zero_add, add_zero, smul_mul_assoc, one_mul]
    exact this
  | succ a ih =>
    intro t b
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    simp only [Om, List.take_succ_cons, List.drop_succ_cons, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc]
    congr 1
    have := ih (fun y => φ1 (x :: y)) (t + 1) b
    rw [show t + (a + 1) = t + 1 + a by omega]
    exact this

/-! ### Kernels -/

def Fr (t n : ℕ) (u : FreeGroup (Fin d)) : Mt L :=
  Om L t n (fun w => if wordFree w = u then 1 else 0)

def FPc (v : FreeGroup (Fin d)) (w : List (Letter d)) : Prop :=
  wordFree w = v ∧ ∀ l, 1 ≤ l → l < w.length → wordFree (w.drop l) ≠ v

def FP (t n : ℕ) (v : FreeGroup (Fin d)) : Mt L :=
  Om L t n (fun w => if FPc v w then 1 else 0)

lemma ite_mul_ite (A B : Prop) [Decidable A] [Decidable B] : ((if A then (1 : ℂ) else 0) * (if B then 1 else 0)) =
    if A ∧ B then 1 else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

lemma wordFree_split (w : List (Letter d)) (n : ℕ) :
    wordFree w = wordFree (w.take n) * wordFree (w.drop n) := by
  conv_lhs => rw [← List.take_append_drop n w]
  exact wordFree_append _ _

theorem fr_scalar (V v : FreeGroup (Fin d)) (hv : v ≠ 1) (hs : v.toWord <:+ (V * v).toWord)
    (w : List (Letter d)) :
    ((if wordFree w = V * v then 1 else 0 : ℂ)) =
      ∑ n' ∈ Finset.range (w.length + 1),
        (if wordFree (w.take n') = V then 1 else 0) * (if FPc v (w.drop n') then 1 else 0) := by
  simp_rw [ite_mul_ite]
  by_cases hW : wordFree w = V * v
  · rw [if_pos hW]
    obtain ⟨l0, hl0, hl0v⟩ := walk_hit v w (by rw [hW]; exact hs)
    set P : ℕ → Prop := fun l => wordFree (w.drop l) = v with hP
    set n0 := Nat.findGreatest P w.length with hn0
    have hspec : P n0 := Nat.findGreatest_spec (P := P) hl0 hl0v
    have hn0le : n0 ≤ w.length := Nat.findGreatest_le _
    have hgreat : ∀ k, n0 < k → k ≤ w.length → ¬ P k := fun k hk hkl =>
      Nat.findGreatest_is_greatest hk hkl
    have hmain : ∀ n', n' ≤ w.length →
        ((wordFree (w.take n') = V ∧ FPc v (w.drop n')) ↔ n' = n0) := by
      intro n' hn'
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · -- n' < n0
          have hlen : (w.drop n').length = w.length - n' := List.length_drop
          have hlt2 : n0 - n' < (w.drop n').length := by
            rcases Nat.lt_or_ge n0 w.length with h | h
            · omega
            · have : n0 = w.length := le_antisymm hn0le h
              -- then drop n0 w = [] and wordFree = 1 ≠ v
              exfalso
              have hd : w.drop n0 = [] := by simp [this]
              have := hspec
              simp only [hP, hd, wordFree_nil] at this
              exact hv this.symm
          refine h3 (n0 - n') (by omega) hlt2 ?_
          rw [List.drop_drop, Nat.add_sub_cancel' hlt.le]
          exact hspec
        · exact hgreat n' hgt hn' h2
      · rintro rfl
        refine ⟨?_, hspec, ?_⟩
        · have := wordFree_split w n0
          rw [hW] at this
          have h2 : wordFree (w.drop n0) = v := hspec
          rw [h2] at this
          exact (mul_right_cancel this).symm
        · intro l hl1 hl2 hlv
          rw [List.drop_drop] at hlv
          exact hgreat (n0 + l) (by omega) (by
            have : (w.drop n0).length = w.length - n0 := List.length_drop
            omega) hlv
    rw [Finset.sum_eq_single n0]
    · rw [if_pos]
      exact (hmain n0 hn0le).mpr rfl
    · intro b hb hbne
      rw [if_neg]
      intro hh
      exact hbne ((hmain b (by have := Finset.mem_range.mp hb; omega)).mp hh)
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hW]
    symm
    refine Finset.sum_eq_zero fun n' _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2, _⟩
    apply hW
    rw [wordFree_split w n', h1, h2]

theorem Fr_rec (V v : FreeGroup (Fin d)) (hv : v ≠ 1) (hs : v.toWord <:+ (V * v).toWord)
    (t n : ℕ) :
    Fr L t n (V * v) = ∑ n' ∈ Finset.range (n + 1), Fr L t n' V * FP L (t + n') (n - n') v := by
  unfold Fr FP
  rw [Om_congr L n t _ (fun w => ∑ n' ∈ Finset.range (n + 1),
      (if wordFree (w.take n') = V then (1 : ℂ) else 0) *
        (if FPc v (w.drop n') then 1 else 0))
      (fun w hw => by rw [fr_scalar V v hv hs w, hw]), Om_sum]
  refine Finset.sum_congr rfl fun n' hn' => ?_
  have hle : n' ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn')
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.add_sub_cancel_left]
  exact Om_split L (fun x => if wordFree x = V then (1 : ℂ) else 0)
    (fun y => if FPc v y then (1 : ℂ) else 0) n' t b

/-! ### First passage expansion (Lemma 9.4) -/

def NR (w : List (Letter d)) : Prop := ∀ l, 1 ≤ l → l < w.length → wordFree (w.drop l) ≠ 1

def Rc (w : List (Letter d)) : Prop := wordFree w = 1 ∧ NR w

def γ (s : ℕ) (x : List (Letter d)) : ℂ := if s = 0 then 1 else -(if Rc x then 1 else 0)

def Gam (t s : ℕ) : Mt L := Om L t s (γ s)

lemma Rc_take_iff (v : FreeGroup (Fin d)) (w : List (Letter d)) (hW : wordFree w = v) (i : ℕ)
    (hi : i < w.length) (hv : wordFree (w.drop (i + 1)) = v) :
    Rc (w.take (i + 1)) ↔ ∀ j, j < i → wordFree (w.drop (j + 1)) ≠ v := by
  have hlen : (w.take (i + 1)).length = i + 1 := by simp; omega
  have hsplit : w = w.take (i + 1) ++ w.drop (i + 1) := (List.take_append_drop _ _).symm
  have hx : wordFree (w.take (i + 1)) = 1 := by
    have := wordFree_split w (i + 1)
    rw [hW, hv] at this
    exact (mul_eq_right.mp this.symm)
  have hj : ∀ j, j < i → wordFree (w.drop (j + 1)) = wordFree ((w.take (i + 1)).drop (j + 1)) * v := by
    intro j hji
    conv_lhs => rw [hsplit]
    rw [List.drop_append_of_le_length (by omega), wordFree_append, hv]
  constructor
  · rintro ⟨-, hNR⟩ j hji h
    apply hNR (j + 1) (by omega) (by omega)
    rw [hj j hji] at h
    exact mul_eq_right.mp h
  · intro h
    refine ⟨hx, fun l hl1 hl2 => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, l = j + 1 := ⟨l - 1, by omega⟩
    intro h1
    apply h j (by omega)
    rw [hj j (by omega), h1, one_mul]

theorem fp_scalar (v : FreeGroup (Fin d)) (hv : v ≠ 1) (w : List (Letter d)) :
    (if FPc v w then (1 : ℂ) else 0) = ∑ s ∈ Finset.range (w.length + 1),
      γ s (w.take s) * (if wordFree (w.drop s) = v then 1 else 0) := by
  rw [Finset.sum_range_succ']
  simp only [γ, List.take_zero, List.drop_zero, if_true, one_mul, Nat.add_one_ne_zero, if_false]
  by_cases hW : wordFree w = v
  · rw [if_pos hW]
    simp_rw [neg_mul, ite_mul_ite, Finset.sum_neg_distrib, Finset.sum_boole]
    set n := w.length with hn
    set Zs := (Finset.range n).filter (fun i => wordFree (w.drop (i + 1)) = v) with hZs
    have hfil : ((Finset.range n).filter (fun i => Rc (w.take (i + 1)) ∧
        wordFree (w.drop (i + 1)) = v)) = (Zs.filter fun i => ∀ j, j < i → j ∉ Zs) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, hZs]
      constructor
      · rintro ⟨hi, hR, hvi⟩
        refine ⟨⟨hi, hvi⟩, fun j hj hjZ => ?_⟩
        exact (Rc_take_iff v w hW i hi hvi).mp hR j hj hjZ.2
      · rintro ⟨⟨hi, hvi⟩, hj⟩
        refine ⟨hi, (Rc_take_iff v w hW i hi hvi).mpr fun j hji hjv => ?_, hvi⟩
        exact hj j hji ⟨by omega, hjv⟩
    rw [hfil]
    by_cases hZ : Zs.Nonempty
    · set i0 := Zs.min' hZ with hi0
      have hcard : (Zs.filter fun i => ∀ j, j < i → j ∉ Zs) = {i0} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hiZ, hj⟩
          have h1 : i0 ≤ i := Finset.min'_le _ _ hiZ
          by_contra hne
          exact hj i0 (lt_of_le_of_ne h1 (Ne.symm hne)) (Finset.min'_mem _ _)
        · rintro rfl
          refine ⟨Finset.min'_mem _ _, fun j hj hjZ => ?_⟩
          exact absurd (Finset.min'_le _ _ hjZ) (not_le.mpr hj)
      rw [hcard, Finset.card_singleton]
      rw [if_neg]
      · norm_num
      · rintro ⟨-, h2⟩
        obtain ⟨i, hiZ⟩ := hZ
        simp only [hZs, Finset.mem_filter, Finset.mem_range] at hiZ
        by_cases hin : i + 1 < n
        · exact h2 (i + 1) (by omega) hin hiZ.2
        · have : i + 1 = n := by omega
          have hd : w.drop (i + 1) = [] := by simp [this, hn]
          rw [hd, wordFree_nil] at hiZ
          exact hv hiZ.2.symm
    · rw [Finset.not_nonempty_iff_eq_empty] at hZ
      have : (Zs.filter fun i => ∀ j, j < i → j ∉ Zs) = ∅ := by simp [hZ]
      rw [this, Finset.card_empty, if_pos]
      · norm_num
      · refine ⟨hW, fun l hl1 hl2 hlv => ?_⟩
        have : l - 1 ∈ Zs := by
          simp only [hZs, Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          rw [show l - 1 + 1 = l by omega]
          exact hlv
        rw [hZ] at this
        simp at this
  · rw [if_neg (fun h => hW h.1), if_neg hW, add_zero]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : wordFree (w.drop (i + 1)) = v
    · by_cases h2 : Rc (w.take (i + 1))
      · exfalso
        apply hW
        rw [wordFree_split w (i + 1), h2.1, h1, one_mul]
      · simp [h2]
    · simp [h1]

theorem FP_expand (v : FreeGroup (Fin d)) (hv : v ≠ 1) (t n : ℕ) :
    FP L t n v = ∑ s ∈ Finset.range (n + 1), Gam L t s * Fr L (t + s) (n - s) v := by
  unfold FP Gam Fr
  rw [Om_congr L n t _ (fun w => ∑ s ∈ Finset.range (n + 1),
      γ s (w.take s) * (if wordFree (w.drop s) = v then (1 : ℂ) else 0))
      (fun w hw => by rw [fp_scalar v hv w, hw]), Om_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))
  rw [Nat.add_sub_cancel_left]
  exact Om_split L (γ s) (fun y => if wordFree y = v then (1 : ℂ) else 0) s t b

/-! ### Convolution of kernels -/

def cv {α : Type*} [NonUnitalNonAssocSemiring α] (F G : ℕ → ℕ → α) : ℕ → ℕ → α :=
  fun t n => ∑ a ∈ Finset.range (n + 1), F t a * G (t + a) (n - a)

theorem cv_assoc {α : Type*} [NonUnitalSemiring α] (A B C : ℕ → ℕ → α) :
    cv (cv A B) C = cv A (cv B C) := by
  funext t n
  simp only [cv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun b => Finset.Ico b (n + 1))]
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.sum_Ico_eq_sum_range]
    have hb' : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    rw [show n + 1 - b = n - b + 1 by omega]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nat.add_sub_cancel_left, mul_assoc, ← add_assoc, Nat.sub_add_eq]
  · intro a b
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

def chainR {α : Type*} [NonUnitalNonAssocSemiring α] (k : ℕ → ℕ → α) :
    List (ℕ → ℕ → α) → (ℕ → ℕ → α)
  | [] => k
  | k' :: ks => cv k (chainR k' ks)

theorem chainR_snoc {α : Type*} [NonUnitalSemiring α] (ks : List (ℕ → ℕ → α)) :
    ∀ (k Z : ℕ → ℕ → α), cv (chainR k ks) Z = chainR k (ks ++ [Z]) := by
  induction ks with
  | nil => intro k Z; rfl
  | cons k' ks ih =>
    intro k Z
    simp only [chainR, List.cons_append]
    rw [cv_assoc, ih]

/-! ### Chains of blocks -/

def FrK (u : FreeGroup (Fin d)) : ℕ → ℕ → Mt L := fun t n => Fr L t n u

def FPK (v : FreeGroup (Fin d)) : ℕ → ℕ → Mt L := fun t n => FP L t n v

theorem Fr_rec_cv (V v : FreeGroup (Fin d)) (hv : v ≠ 1) (hs : v.toWord <:+ (V * v).toWord) :
    FrK L (V * v) = cv (FrK L V) (FPK L v) := by
  funext t n
  exact Fr_rec L V v hv hs t n

theorem FPK_eq (v : FreeGroup (Fin d)) (hv : v ≠ 1) :
    FPK L v = cv (Gam L) (FrK L v) := by
  funext t n
  exact FP_expand L v hv t n

def blockList (Bs : List (List (Fin d × Bool))) : List (ℕ → ℕ → Mt L) :=
  Bs.flatMap fun B => [Gam L, FrK L (FreeGroup.mk B)]

theorem Fr_chain (B1 : List (Fin d × Bool)) :
    ∀ (Bs : List (List (Fin d × Bool))), (∀ B ∈ Bs, B ≠ []) →
      FreeGroup.IsReduced (B1 ++ Bs.flatten) →
      FrK L (FreeGroup.mk (B1 ++ Bs.flatten)) = chainR (FrK L (FreeGroup.mk B1)) (blockList L Bs) := by
  intro Bs
  induction Bs using List.reverseRecOn with
  | nil => intro _ _; simp [blockList, chainR]
  | append_singleton Bs' B ih =>
    intro hne hred
    have hBne : B ≠ [] := hne B (by simp)
    have hne' : ∀ B' ∈ Bs', B' ≠ [] := fun B' h => hne B' (by simp [h])
    rw [List.flatten_append, List.flatten_singleton, ← List.append_assoc] at hred ⊢
    have hredP : FreeGroup.IsReduced (B1 ++ Bs'.flatten) := hred.infix ⟨[], B, by simp⟩
    have hredB : FreeGroup.IsReduced B := hred.infix ⟨B1 ++ Bs'.flatten, [], by simp⟩
    have hmkB : (FreeGroup.mk B).toWord = B := by
      rw [FreeGroup.toWord_mk]; exact hredB.reduce_eq
    have hmkPB : (FreeGroup.mk (B1 ++ Bs'.flatten ++ B)).toWord = B1 ++ Bs'.flatten ++ B := by
      rw [FreeGroup.toWord_mk]; exact hred.reduce_eq
    have hv : FreeGroup.mk B ≠ 1 := by
      intro h
      have := congrArg FreeGroup.toWord h
      rw [hmkB, FreeGroup.toWord_one] at this
      exact hBne this
    have hs : (FreeGroup.mk B).toWord <:+ (FreeGroup.mk (B1 ++ Bs'.flatten) * FreeGroup.mk B).toWord := by
      rw [FreeGroup.mul_mk, hmkPB, hmkB]
      exact List.suffix_append _ _
    rw [← FreeGroup.mul_mk, Fr_rec_cv L _ _ hv hs, FPK_eq L _ hv, ih hne' hredP]
    simp only [blockList, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← cv_assoc, chainR_snoc, chainR_snoc]
    simp

/-! ### Operators -/

open StrongConv.S9.PartLin
open scoped InnerProductSpace

abbrev Vec := PiLp 2 (fun _ : Fin L.Dm => L2Free d)

def ev (y : Fin L.Dm) : Vec L := PiLp.single 2 y (delta (1 : FreeGroup (Fin d)))

lemma ev_apply (y x : Fin L.Dm) (u : FreeGroup (Fin d)) :
    (ev L y) x u = if x = y then (if u = 1 then 1 else 0) else 0 := by
  by_cases h : x = y
  · subst h
    by_cases hu : u = 1 <;> simp [ev, delta, lp.single_apply, hu, Pi.single_apply]
  · simp [ev, h]

lemma ev_norm (y : Fin L.Dm) : ‖ev L y‖ = 1 := by
  simp [ev, delta]

lemma X_apply (j : ℕ) (z : Vec L) (x : Fin L.Dm) (u : FreeGroup (Fin d)) :
    (Xop L j z) x u = ∑ x', ∑ a : Letter d, L.B j a x x' * (z x') ((gl a)⁻¹ * u) := by
  unfold Xop linOp
  simp only [ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, tr_tensorOp_apply,
    lp.coeFn_sum, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, wordEval_sLimit, leftReg_apply]
  rw [Finset.sum_comm]
  rfl

def XP : ℕ → ℕ → (Vec L →L[ℂ] Vec L)
  | _, 0 => 1
  | t, n + 1 => Xop L t * XP (t + 1) n

theorem Fr_succ (t n : ℕ) (u : FreeGroup (Fin d)) :
    Fr L t (n + 1) u = ∑ a : Letter d, L.B t a * Fr L (t + 1) n ((gl a)⁻¹ * u) := by
  unfold Fr
  simp only [Om]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  apply Om_congr
  intro w _
  simp [wordFree_cons, eq_inv_mul_iff_mul_eq]

theorem Fr_entry : ∀ (n t : ℕ) (u : FreeGroup (Fin d)) (x y : Fin L.Dm),
    Fr L t n u x y = (XP L t n (ev L y)) x u
  | 0, t, u, x, y => by
    simp only [Fr, Om, XP, wordFree_nil, ContinuousLinearMap.one_apply]
    rw [ev_apply]
    by_cases hxy : x = y <;> by_cases hu : u = 1 <;> simp [hxy, hu, Matrix.one_apply, eq_comm]
  | n + 1, t, u, x, y => by
    rw [Fr_succ]
    simp only [XP, ContinuousLinearMap.mul_apply]
    rw [X_apply]
    simp only [Matrix.sum_apply, Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Fr_entry n (t + 1) _ x' y]

theorem XP_norm (ρ : ℝ) (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) : ∀ n t, ‖XP L t n‖ ≤ ρ ^ n := by
  intro n
  induction n with
  | zero =>
    intro t
    have : XP L t 0 = ContinuousLinearMap.id ℂ _ := rfl
    rw [this, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    intro t
    have h0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
    have : XP L t (n + 1) = Xop L t * XP L (t + 1) n := rfl
    rw [this, pow_succ']
    have hc : ‖(Xop L t).comp (XP L (t + 1) n)‖ ≤ ‖Xop L t‖ * ‖XP L (t + 1) n‖ :=
      ContinuousLinearMap.opNorm_comp_le (Xop L t) (XP L (t + 1) n)
    exact hc.trans (mul_le_mul (hρ t) (ih (t + 1)) (norm_nonneg _) h0)

lemma entry_le (Z : Vec L) (x : Fin L.Dm) (u : FreeGroup (Fin d)) : ‖Z x u‖ ≤ ‖Z‖ :=
  (lp.norm_apply_le_norm (by simp) (Z x) u).trans (PiLp.norm_apply_le Z x)

lemma bessel (Z : Vec L) (S : Finset (FreeGroup (Fin d))) :
    ∑ x, ∑ u ∈ S, ‖Z x u‖ ^ 2 ≤ ‖Z‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_le_sum fun x _ => ?_
  have := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) (Z x) S
  simpa using this

theorem Fr_entry_le (ρ : ℝ) (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t n : ℕ) (u : FreeGroup (Fin d))
    (x y : Fin L.Dm) : ‖Fr L t n u x y‖ ≤ ρ ^ n := by
  rw [Fr_entry]
  refine (entry_le L _ x u).trans ?_
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [ev_norm, mul_one]
  exact XP_norm L ρ hρ n t

theorem Fr_bessel (ρ : ℝ) (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t n : ℕ) (S : Finset (FreeGroup (Fin d)))
    (y : Fin L.Dm) : ∑ x, ∑ u ∈ S, ‖Fr L t n u x y‖ ^ 2 ≤ ρ ^ (2 * n) := by
  simp_rw [Fr_entry]
  refine (bessel L _ S).trans ?_
  have h0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
  have : ‖XP L t n (ev L y)‖ ≤ ρ ^ n := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ev_norm, mul_one]
    exact XP_norm L ρ hρ n t
  calc ‖XP L t n (ev L y)‖ ^ 2 ≤ (ρ ^ n) ^ 2 := by gcongr
    _ = ρ ^ (2 * n) := by rw [← pow_mul, mul_comm]

/-! ### The projection `Q` -/

def Qop : L2Free d →L[ℂ] L2Free d :=
  ContinuousLinearMap.id ℂ _ - (innerSL ℂ (delta (1 : FreeGroup (Fin d)))).smulRight (delta 1)

lemma Qop_apply (f : L2Free d) (u : FreeGroup (Fin d)) :
    Qop f u = if u = 1 then 0 else f u := by
  have h1 : (innerSL ℂ (delta (1 : FreeGroup (Fin d)))) f = f 1 := by
    simp [delta, lp.inner_single_left]
  simp only [Qop, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, h1, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  by_cases hu : u = 1
  · subst hu; simp [delta, lp.single_apply]
  · simp [delta, lp.single_apply, hu, Pi.single_apply]

lemma Qop_norm (f : L2Free d) : ‖Qop f‖ ≤ ‖f‖ := by
  have h1 : f = Qop f + (f 1) • delta (1 : FreeGroup (Fin d)) := by
    ext u
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Qop_apply]
    by_cases hu : u = 1
    · subst hu; simp [delta, lp.single_apply]
    · simp [delta, lp.single_apply, hu, Pi.single_apply]
  have h2 : inner ℂ (Qop f) ((f 1) • delta (1 : FreeGroup (Fin d))) = 0 := by
    rw [inner_smul_right]
    simp [delta, lp.inner_single_right, Qop_apply]
  have h3 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (Qop f) _ h2
  rw [← h1] at h3
  by_contra hcon
  have hcon := not_le.mp hcon
  nlinarith [norm_nonneg (Qop f), norm_nonneg f, mul_self_nonneg ‖(f 1) • delta (1 : FreeGroup (Fin d))‖]

def Qt : Vec L →L[ℂ] Vec L := tensorOp (1 : Matrix (Fin L.Dm) (Fin L.Dm) ℂ) (Qop (d := d))

lemma Qt_apply (z : Vec L) (x : Fin L.Dm) : (Qt L z) x = Qop (z x) := by
  simp [Qt, tr_tensorOp_apply, Matrix.one_apply]

lemma Qt_norm : ‖Qt L‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  have h1 : ‖Qt L z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Qt_apply]
    exact pow_le_pow_left₀ (norm_nonneg _) (Qop_norm _) 2
  exact le_of_sq_le_sq h1 (norm_nonneg _)

theorem Om_succ (t n : ℕ) (φ : List (Letter d) → ℂ) :
    Om L t (n + 1) φ = ∑ a : Letter d, L.B t a * Om L (t + 1) n (fun w => φ (a :: w)) := rfl

def YQ : ℕ → ℕ → (Vec L →L[ℂ] Vec L)
  | t, 0 => Xop L t
  | t, s + 1 => Xop L t * Qt L * YQ (t + 1) s

theorem YQ_norm (ρ : ℝ) (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) : ∀ s t, ‖YQ L t s‖ ≤ ρ ^ (s + 1) := by
  intro s
  induction s with
  | zero => intro t; simpa [YQ] using hρ t
  | succ s ih =>
    intro t
    have h0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
    have : YQ L t (s + 1) = ((Xop L t).comp (Qt L)).comp (YQ L (t + 1) s) := rfl
    rw [this, pow_succ' ρ (s + 1)]
    have hc1 : ‖(Xop L t).comp (Qt L)‖ ≤ ‖Xop L t‖ * ‖Qt L‖ :=
      ContinuousLinearMap.opNorm_comp_le (Xop L t) (Qt L)
    have hc2 : ‖((Xop L t).comp (Qt L)).comp (YQ L (t + 1) s)‖ ≤
        ‖(Xop L t).comp (Qt L)‖ * ‖YQ L (t + 1) s‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h1 : ‖(Xop L t).comp (Qt L)‖ ≤ ρ := by
      refine hc1.trans ?_
      calc ‖Xop L t‖ * ‖Qt L‖ ≤ ρ * 1 :=
            mul_le_mul (hρ t) (Qt_norm L) (norm_nonneg _) h0
        _ = ρ := mul_one _
    exact hc2.trans (mul_le_mul h1 (ih (t + 1)) (norm_nonneg _) h0)

lemma NR_cons (a : Letter d) (w : List (Letter d)) (hw : w ≠ []) :
    NR (a :: w) ↔ wordFree w ≠ 1 ∧ NR w := by
  have hlen : 1 ≤ w.length := List.length_pos_iff.mpr hw
  constructor
  · intro h
    refine ⟨?_, fun l hl1 hl2 => ?_⟩
    · have := h 1 le_rfl (by simp; omega)
      simpa using this
    · have := h (l + 1) (by omega) (by simp; omega)
      simpa using this
  · rintro ⟨h1, h2⟩ l hl1 hl2
    by_cases hl : l = 1
    · subst hl; simpa using h1
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have := h2 l' (by omega) (by simp at hl2; omega)
      simpa using this

theorem YQ_entry : ∀ (s t : ℕ) (u : FreeGroup (Fin d)) (x y : Fin L.Dm),
    (YQ L t s (ev L y)) x u =
      Om L t (s + 1) (fun w => if wordFree w = u ∧ NR w then 1 else 0) x y
  | 0, t, u, x, y => by
    have : YQ L t 0 = Xop L t := rfl
    rw [this, X_apply]
    simp only [Om, Matrix.sum_apply, Matrix.mul_apply, ev_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h1 : wordFree [a] = gl a := rfl
    have h2 : ((if wordFree [a] = u ∧ NR [a] then (1 : ℂ) else 0) • (1 : Mt L)) = 
        (if gl a = u then (1 : ℂ) else 0) • (1 : Mt L) := by
      have : NR [a] := fun l hl1 hl2 => by simp at hl2; omega
      simp [h1, this]
    rw [h2]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hg : gl a = u
    · simp [hg]
    · have : (gl a)⁻¹ * u ≠ 1 := fun h => hg (inv_mul_eq_one.mp h)
      simp [hg, this]
  | s + 1, t, u, x, y => by
    have : YQ L t (s + 1) = ((Xop L t).comp (Qt L)).comp (YQ L (t + 1) s) := rfl
    rw [this]
    simp only [ContinuousLinearMap.comp_apply]
    rw [X_apply]
    simp only [Qt_apply, Qop_apply, YQ_entry s (t + 1)]
    rw [Om_succ]
    simp only [Matrix.sum_apply, Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x' _ => ?_
    congr 1
    by_cases hv : (gl a)⁻¹ * u = 1
    · rw [if_pos hv]
      have : Om L (t + 1) (s + 1) (fun w => if wordFree (a :: w) = u ∧ NR (a :: w) then (1 : ℂ) else 0)
          = 0 := by
        rw [← Om_zero L (s + 1) (t + 1)]
        apply Om_congr
        intro w hw
        have hne : w ≠ [] := by rintro rfl; simp at hw
        rw [if_neg]
        rintro ⟨h1, h2⟩
        rw [NR_cons a w hne] at h2
        rw [wordFree_cons] at h1
        apply h2.1
        have : wordFree w = (gl a)⁻¹ * u := by rw [← h1]; group
        rw [this, hv]
      rw [this]; simp
    · rw [if_neg hv]
      have : Om L (t + 1) (s + 1) (fun w => if wordFree (a :: w) = u ∧ NR (a :: w) then (1 : ℂ) else 0)
          = Om L (t + 1) (s + 1) (fun w => if wordFree w = (gl a)⁻¹ * u ∧ NR w then 1 else 0) := by
        apply Om_congr
        intro w hw
        have hne : w ≠ [] := by rintro rfl; simp at hw
        rw [NR_cons a w hne, wordFree_cons]
        by_cases hh : wordFree w = (gl a)⁻¹ * u
        · have : gl a * wordFree w = u := by rw [hh]; group
          simp [hh, this, hv]
        · have : ¬ gl a * wordFree w = u := fun h => hh (by rw [← h]; group)
          simp [hh, this]
      rw [this]

theorem Gam_entry_le (ρ : ℝ) (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t s : ℕ) (x y : Fin L.Dm) :
    ‖Gam L t s x y‖ ≤ ρ ^ s := by
  cases s with
  | zero =>
    simp only [Gam, Om, γ, if_true, pow_zero]
    by_cases hxy : x = y <;> simp [hxy, Matrix.one_apply]
  | succ s =>
    have h : Gam L t (s + 1) = (-1 : ℂ) • Om L t (s + 1) (fun w => if Rc w then 1 else 0) := by
      unfold Gam
      rw [← Om_smul]
      apply Om_congr
      intro w _
      by_cases hr : Rc w <;> simp [γ, hr]
    rw [h, Matrix.smul_apply, smul_eq_mul]
    have h2 : Om L t (s + 1) (fun w => if Rc w then (1 : ℂ) else 0) x y =
        (YQ L t s (ev L y)) x 1 := by
      rw [YQ_entry]
      have : Om L t (s + 1) (fun w => if Rc w then (1 : ℂ) else 0) =
          Om L t (s + 1) (fun w => if wordFree w = 1 ∧ NR w then 1 else 0) := by
        apply Om_congr
        intro w _
        simp only [Rc]
        congr
      rw [this]
    rw [h2, neg_one_mul, norm_neg]
    refine (entry_le L _ x 1).trans ?_
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ev_norm, mul_one]
    exact YQ_norm L ρ hρ s t

/-! ### Real kernels -/

abbrev RK := ℕ → ℕ → ℝ

def RNN (k : RK) : Prop := ∀ t n, 0 ≤ k t n

def RLE (k k' : RK) : Prop := ∀ t n, k t n ≤ k' t n

theorem cv_nonneg {A B : RK} (hA : RNN A) (hB : RNN B) : RNN (cv A B) := fun t n =>
  Finset.sum_nonneg fun a _ => mul_nonneg (hA _ _) (hB _ _)

theorem cv_mono {A A' B B' : RK} (hA : RNN A) (hB : RNN B) (hAA : RLE A A') (hBB : RLE B B') :
    RLE (cv A B) (cv A' B') := fun t n =>
  Finset.sum_le_sum fun a _ =>
    mul_le_mul (hAA _ _) (hBB _ _) (hB _ _) ((hA _ _).trans (hAA _ _))

theorem cv_sum_right {ι : Type*} (S : Finset ι) (A : RK) (X : ι → RK) (t n : ℕ) :
    ∑ i ∈ S, cv A (X i) t n = cv A (fun t n => ∑ i ∈ S, X i t n) t n := by
  simp only [cv, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem cv_sum_left {ι : Type*} (S : Finset ι) (A : ι → RK) (X : RK) (t n : ℕ) :
    ∑ i ∈ S, cv (A i) X t n = cv (fun t n => ∑ i ∈ S, A i t n) X t n := by
  simp only [cv, Finset.sum_mul]
  rw [Finset.sum_comm]

def chainL {α : Type*} [NonUnitalNonAssocSemiring α] :
    List (ℕ → ℕ → α) → (ℕ → ℕ → α) → (ℕ → ℕ → α)
  | [], q => q
  | m :: ms, q => cv m (chainL ms q)

theorem chainL_append {α : Type*} [NonUnitalNonAssocSemiring α] (l1 l2 : List (ℕ → ℕ → α))
    (q : ℕ → ℕ → α) : chainL (l1 ++ l2) q = chainL l1 (chainL l2 q) := by
  induction l1 with
  | nil => rfl
  | cons m l1 ih => simp only [List.cons_append, chainL, ih]

theorem chainR_eq_chainL {α : Type*} [NonUnitalNonAssocSemiring α] (ms : List (ℕ → ℕ → α)) :
    ∀ (k q : ℕ → ℕ → α), chainR k (ms ++ [q]) = cv k (chainL ms q) := by
  induction ms with
  | nil => intro k q; rfl
  | cons m ms ih =>
    intro k q
    simp only [List.cons_append, chainR, chainL, ih]

theorem chainL_nonneg : ∀ (ms : List RK) (q : RK), (∀ m ∈ ms, RNN m) → RNN q → RNN (chainL ms q)
  | [], q, _, hq => hq
  | m :: ms, q, hms, hq =>
    cv_nonneg (hms m (by simp)) (chainL_nonneg ms q (fun m' h => hms m' (by simp [h])) hq)

theorem chainL_mono : ∀ (ms ms' : List RK) (q q' : RK), List.Forall₂ (fun a b => RNN a ∧ RLE a b) ms ms' →
    RNN q → RLE q q' → RNN (chainL ms q) ∧ RLE (chainL ms q) (chainL ms' q')
  | [], [], q, q', _, hq, hqq => ⟨hq, hqq⟩
  | [], _ :: _, q, q', h, hq, hqq => by cases h
  | _ :: _, [], q, q', h, hq, hqq => by cases h
  | m :: ms, m' :: ms', q, q', h, hq, hqq => by
    obtain ⟨⟨hm, hmm⟩, h'⟩ := List.forall₂_cons.mp h
    obtain ⟨h1, h2⟩ := chainL_mono ms ms' q q' h' hq hqq
    exact ⟨cv_nonneg hm h1, cv_mono hm h1 hmm h2⟩

def Bd (c : ℝ) (i : ℕ) (ρ : ℝ) : RK := fun _ n => c * ((n : ℝ) + 1) ^ i * ρ ^ n

theorem cv_Bd {ρ : ℝ} (hρ : 0 ≤ ρ) {A B : RK} (hA : RNN A) (hB : RNN B) {a b : ℝ} {i j : ℕ}
    (hAB : RLE A (Bd a i ρ)) (hBB : RLE B (Bd b j ρ)) :
    RLE (cv A B) (Bd (a * b) (i + j + 1) ρ) := by
  intro t n
  have ha : 0 ≤ a := by
    have := (hA t 0).trans (hAB t 0)
    simpa [Bd] using this
  have hb : 0 ≤ b := by
    have := (hB t 0).trans (hBB t 0)
    simpa [Bd] using this
  simp only [cv, Bd]
  calc ∑ a' ∈ Finset.range (n + 1), A t a' * B (t + a') (n - a')
      ≤ ∑ a' ∈ Finset.range (n + 1), (a * ((n : ℝ) + 1) ^ i * (b * ((n : ℝ) + 1) ^ j) * ρ ^ n) := by
        refine Finset.sum_le_sum fun a' ha' => ?_
        have hle : a' ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha')
        have h1 := hAB t a'
        have h2 := hBB (t + a') (n - a')
        simp only [Bd] at h1 h2
        have h3 : A t a' * B (t + a') (n - a') ≤
            (a * ((a' : ℝ) + 1) ^ i * ρ ^ a') * (b * (((n - a' : ℕ) : ℝ) + 1) ^ j * ρ ^ (n - a')) :=
          mul_le_mul h1 h2 (hB _ _) (by positivity)
        refine h3.trans ?_
        have e1 : ((a' : ℝ) + 1) ^ i ≤ ((n : ℝ) + 1) ^ i :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hle) i
        have e2 : (((n - a' : ℕ) : ℝ) + 1) ^ j ≤ ((n : ℝ) + 1) ^ j :=
          pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ (Nat.sub_le n a')) j
        have e3 : ρ ^ a' * ρ ^ (n - a') = ρ ^ n := by rw [← pow_add, Nat.add_sub_cancel' hle]
        calc (a * ((a' : ℝ) + 1) ^ i * ρ ^ a') * (b * (((n - a' : ℕ) : ℝ) + 1) ^ j * ρ ^ (n - a'))
            = (a * ((a' : ℝ) + 1) ^ i) * (b * (((n - a' : ℕ) : ℝ) + 1) ^ j) *
                (ρ ^ a' * ρ ^ (n - a')) := by ring
          _ ≤ (a * ((n : ℝ) + 1) ^ i) * (b * ((n : ℝ) + 1) ^ j) * ρ ^ n := by
              rw [e3]
              gcongr
      _ = (a * b) * ((n : ℝ) + 1) ^ (i + j + 1) * ρ ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

theorem chainL_Bd {ρ : ℝ} (hρ : 0 ≤ ρ) {c : ℝ} (hc : 0 ≤ c) : ∀ (ms : List RK) (q : RK),
    (∀ m ∈ ms, RNN m ∧ RLE m (Bd c 0 ρ)) → RNN q → RLE q (Bd c 0 ρ) →
    RLE (chainL ms q) (Bd (c ^ (ms.length + 1)) ms.length ρ)
  | [], q, _, _, hq => by
    intro t n
    have := hq t n
    simp only [chainL, List.length_nil, Bd] at this ⊢
    simpa using this
  | m :: ms, q, hms, hq0, hq => by
    have ih := chainL_Bd hρ hc ms q (fun m' h => hms m' (by simp [h])) hq0 hq
    have hnn := chainL_nonneg ms q (fun m' h => (hms m' (by simp [h])).1) hq0
    have := cv_Bd hρ (hms m (by simp)).1 hnn (hms m (by simp)).2 ih
    intro t n
    have h := this t n
    show cv m (chainL ms q) t n ≤ _
    refine h.trans (le_of_eq ?_)
    simp only [Bd, List.length_cons, zero_add]
    rw [pow_succ' c (ms.length + 1)]

theorem cvR_sum {ι : Type*} (S : Finset ι) (A : RK) (X : ι → RK) :
    (fun t n => ∑ i ∈ S, cv A (X i) t n) = cv A (fun t n => ∑ i ∈ S, X i t n) :=
  funext fun t => funext fun n => cv_sum_right S A X t n

theorem cvL_sum {ι : Type*} (S : Finset ι) (A : ι → RK) (X : RK) :
    (fun t n => ∑ i ∈ S, cv (A i) X t n) = cv (fun t n => ∑ i ∈ S, A i t n) X :=
  funext fun t => funext fun n => cv_sum_left S A X t n

theorem collapse_aux {ι : Type*} (S : Finset ι) (p q : ι → RK) (e1 e2 : RK)
    (hpair : ∀ t1 t2 a c, ∑ i ∈ S, p i t1 a * q i t2 c ≤ e1 t1 a * e2 t2 c)
    (hp : ∀ i, RNN (p i)) :
    ∀ (ms : List RK), (∀ m ∈ ms, RNN m) → ∀ tp a t' n',
      ∑ i ∈ S, p i tp a * chainL ms (q i) t' n' ≤ e1 tp a * chainL ms e2 t' n'
  | [], _, tp, a, t', n' => hpair tp t' a n'
  | m :: ms, hms, tp, a, t', n' => by
    have ih := collapse_aux S p q e1 e2 hpair hp ms (fun m' h => hms m' (by simp [h]))
    have hm := hms m (by simp)
    show ∑ i ∈ S, p i tp a * cv m (chainL ms (q i)) t' n' ≤ e1 tp a * cv m (chainL ms e2) t' n'
    simp only [cv, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b _ => ?_
    calc ∑ i ∈ S, p i tp a * (m t' b * chainL ms (q i) (t' + b) (n' - b))
        = m t' b * ∑ i ∈ S, p i tp a * chainL ms (q i) (t' + b) (n' - b) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ m t' b * (e1 tp a * chainL ms e2 (t' + b) (n' - b)) :=
          mul_le_mul_of_nonneg_left (ih tp a _ _) (hm _ _)
      _ = e1 tp a * (m t' b * chainL ms e2 (t' + b) (n' - b)) := by ring

theorem collapse {ι : Type*} (S : Finset ι) (p q : ι → RK) (e1 e2 : RK)
    (hpair : ∀ t1 t2 a c, ∑ i ∈ S, p i t1 a * q i t2 c ≤ e1 t1 a * e2 t2 c)
    (hp : ∀ i, RNN (p i)) (ms : List RK) (hms : ∀ m ∈ ms, RNN m) (t n : ℕ) :
    ∑ i ∈ S, cv (p i) (chainL ms (q i)) t n ≤ cv e1 (chainL ms e2) t n := by
  simp only [cv]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun a _ => collapse_aux S p q e1 e2 hpair hp ms hms t a _ _

theorem ctx_sum_le {ι : Type*} (S : Finset ι) (A B R Xe : RK) (X : ι → RK)
    (hA : RNN A) (hB : RNN B) (hR : RNN R) (hX : ∀ i, RNN (X i)) (hXe : RNN Xe)
    (hle : ∀ t n, ∑ i ∈ S, X i t n ≤ Xe t n) (t n : ℕ) :
    ∑ i ∈ S, cv A (cv B (cv (X i) R)) t n ≤ cv A (cv B (cv Xe R)) t n := by
  have hS : RNN (fun t n => ∑ i ∈ S, X i t n) := fun t n => Finset.sum_nonneg fun i _ => hX i t n
  have e : (fun t n => ∑ i ∈ S, cv A (cv B (cv (X i) R)) t n) =
      cv A (cv B (cv (fun t n => ∑ i ∈ S, X i t n) R)) := by
    rw [cvR_sum S A (fun i => cv B (cv (X i) R)), cvR_sum S B (fun i => cv (X i) R),
      cvL_sum S X R]
  have h1 : RLE (cv (fun t n => ∑ i ∈ S, X i t n) R) (cv Xe R) :=
    cv_mono hS hR hle (fun _ _ => le_rfl)
  have h2 : RLE (cv B (cv (fun t n => ∑ i ∈ S, X i t n) R)) (cv B (cv Xe R)) :=
    cv_mono hB (cv_nonneg hS hR) (fun _ _ => le_rfl) h1
  have h3 := cv_mono hA (cv_nonneg hB (cv_nonneg hS hR)) (fun _ _ => le_rfl) h2
  exact le_of_eq_of_le (congrFun (congrFun e t) n) (h3 t n)

theorem Bd_congr {c c' : ℝ} {i i' : ℕ} (ρ : ℝ) (h1 : c = c') (h2 : i = i') : Bd c i ρ = Bd c' i' ρ := by
  subst h1 h2; rfl

theorem two_pair {ι κ : Type*} (Sg : Finset ι) (Sw : Finset κ) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (Fg Fg' : ι → RK) (Fw : κ → RK) (Γ e1 e2 e1' e2' : RK) (post : List RK)
    (hFg : ∀ g, RNN (Fg g)) (hFw : ∀ w, RNN (Fw w))
    (hΓ : RNN Γ ∧ RLE Γ (Bd c 0 ρ)) (hpost : ∀ m ∈ post, RNN m ∧ RLE m (Bd c 0 ρ))
    (he1 : RNN e1 ∧ RLE e1 (Bd c 0 ρ)) (he2 : RNN e2 ∧ RLE e2 (Bd c 0 ρ))
    (he1' : RNN e1' ∧ RLE e1' (Bd c 0 ρ)) (he2' : RNN e2' ∧ RLE e2' (Bd c 0 ρ))
    (pg : ∀ t1 t2 a n, ∑ g ∈ Sg, Fg g t1 a * Fg' g t2 n ≤ e1 t1 a * e2 t2 n)
    (pw : ∀ t1 t2 a n, ∑ w ∈ Sw, Fw w t1 a * Fw w t2 n ≤ e1' t1 a * e2' t2 n) (t n : ℕ) :
    ∑ g ∈ Sg, ∑ w ∈ Sw, cv (Fg g) (chainL ([Γ, Fw w, Γ, Fw w] ++ post) (Fg' g)) t n ≤
      Bd (c ^ (post.length + 6)) (post.length + 5) ρ t n := by
  rw [Finset.sum_comm]
  have hms : ∀ w, ∀ m ∈ [Γ, Fw w, Γ, Fw w] ++ post, RNN m := by
    intro w m hm
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hm
    rcases hm with rfl | rfl | rfl | rfl | h
    · exact hΓ.1
    · exact hFw w
    · exact hΓ.1
    · exact hFw w
    · exact (hpost m h).1
  set R := chainL post e2 with hR
  have hRnn : RNN R := chainL_nonneg post e2 (fun m h => (hpost m h).1) he2.1
  have s2 : ∀ w ∈ Sw, ∑ g ∈ Sg, cv (Fg g) (chainL ([Γ, Fw w, Γ, Fw w] ++ post) (Fg' g)) t n ≤
      cv e1 (cv Γ (cv (cv (Fw w) (cv Γ (Fw w))) R)) t n := by
    intro w _
    have := collapse Sg Fg Fg' e1 e2 pg hFg ([Γ, Fw w, Γ, Fw w] ++ post) (hms w) t n
    refine this.trans (le_of_eq ?_)
    rw [chainL_append]
    simp only [chainL, cv_assoc]
    all_goals rfl
  refine (Finset.sum_le_sum s2).trans ?_
  have hX : ∀ w, RNN (cv (Fw w) (cv Γ (Fw w))) := fun w =>
    cv_nonneg (hFw w) (cv_nonneg hΓ.1 (hFw w))
  have hXe : RNN (cv e1' (cv Γ e2')) := cv_nonneg he1'.1 (cv_nonneg hΓ.1 he2'.1)
  have hle : ∀ t n, ∑ w ∈ Sw, cv (Fw w) (cv Γ (Fw w)) t n ≤ cv e1' (cv Γ e2') t n := fun t n =>
    collapse Sw Fw Fw e1' e2' pw hFw [Γ] (by simpa using hΓ.1) t n
  refine (ctx_sum_le Sw e1 Γ R (cv e1' (cv Γ e2')) (fun w => cv (Fw w) (cv Γ (Fw w))) he1.1 hΓ.1
    hRnn hX hXe hle t n).trans ?_
  have e : cv e1 (cv Γ (cv (cv e1' (cv Γ e2')) R)) =
      cv e1 (chainL ([Γ, e1', Γ, e2'] ++ post) e2) := by
    rw [chainL_append]
    simp only [chainL, cv_assoc]
    all_goals rfl
  rw [e]
  have h1 : ∀ m ∈ [Γ, e1', Γ, e2'] ++ post, RNN m ∧ RLE m (Bd c 0 ρ) := by
    intro m hm
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hm
    rcases hm with rfl | rfl | rfl | rfl | h
    · exact hΓ
    · exact he1'
    · exact hΓ
    · exact he2'
    · exact hpost m h
  have h2 := chainL_Bd hρ hc ([Γ, e1', Γ, e2'] ++ post) e2 h1 he2.1 he2.2
  have h3 := cv_Bd hρ he1.1 (chainL_nonneg _ e2 (fun m hm => (h1 m hm).1) he2.1) he1.2 h2
  have h4 := h3 t n
  rw [Bd_congr ρ (show c * c ^ (([Γ, e1', Γ, e2'] ++ post).length + 1) = c ^ (post.length + 6) by
      simp only [List.length_append, List.length_cons, List.length_nil]; ring)
    (show 0 + ([Γ, e1', Γ, e2'] ++ post).length + 1 = post.length + 5 by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)] at h4
  exact h4

theorem one_pair {κ : Type*} (Sw : Finset κ) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (Fw : κ → RK) (Γ e1' e2' q : RK) (post : List RK)
    (hFw : ∀ w, RNN (Fw w))
    (hΓ : RNN Γ ∧ RLE Γ (Bd c 0 ρ)) (hpost : ∀ m ∈ post, RNN m ∧ RLE m (Bd c 0 ρ))
    (hq : RNN q ∧ RLE q (Bd c 0 ρ))
    (he1' : RNN e1' ∧ RLE e1' (Bd c 0 ρ)) (he2' : RNN e2' ∧ RLE e2' (Bd c 0 ρ))
    (pw : ∀ t1 t2 a n, ∑ w ∈ Sw, Fw w t1 a * Fw w t2 n ≤ e1' t1 a * e2' t2 n) (t n : ℕ) :
    ∑ w ∈ Sw, cv (Fw w) (chainL ([Γ, Fw w] ++ post) q) t n ≤
      Bd (c ^ (post.length + 4)) (post.length + 3) ρ t n := by
  set R := chainL post q with hR
  have hRnn : RNN R := chainL_nonneg post q (fun m h => (hpost m h).1) hq.1
  have hX : ∀ w, RNN (cv (Fw w) (cv Γ (Fw w))) := fun w =>
    cv_nonneg (hFw w) (cv_nonneg hΓ.1 (hFw w))
  have hS : RNN (fun t n => ∑ w ∈ Sw, cv (Fw w) (cv Γ (Fw w)) t n) := fun t n =>
    Finset.sum_nonneg fun w _ => hX w t n
  have hle : ∀ t n, ∑ w ∈ Sw, cv (Fw w) (cv Γ (Fw w)) t n ≤ cv e1' (cv Γ e2') t n := fun t n =>
    collapse Sw Fw Fw e1' e2' pw hFw [Γ] (by simpa using hΓ.1) t n
  have e0 : ∀ w, cv (Fw w) (chainL ([Γ, Fw w] ++ post) q) = cv (cv (Fw w) (cv Γ (Fw w))) R := by
    intro w
    rw [chainL_append]
    simp only [chainL, cv_assoc]
    all_goals rfl
  simp_rw [e0]
  have e1 := congrFun (congrFun (cvL_sum Sw (fun w => cv (Fw w) (cv Γ (Fw w))) R) t) n
  have h1 := cv_mono hS hRnn hle (fun _ _ => le_rfl) t n
  have e : cv (cv e1' (cv Γ e2')) R = cv e1' (chainL ([Γ, e2'] ++ post) q) := by
    rw [chainL_append]
    simp only [chainL, cv_assoc]
    all_goals rfl
  rw [e] at h1
  refine (le_of_eq_of_le e1 h1).trans ?_
  have hh1 : ∀ m ∈ [Γ, e2'] ++ post, RNN m ∧ RLE m (Bd c 0 ρ) := by
    intro m hm
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hm
    rcases hm with rfl | rfl | h
    · exact hΓ
    · exact he2'
    · exact hpost m h
  have h2 := chainL_Bd hρ hc ([Γ, e2'] ++ post) q hh1 hq.1 hq.2
  have h3 := cv_Bd hρ he1'.1 (chainL_nonneg _ q (fun m hm => (hh1 m hm).1) hq.1) he1'.2 h2
  have h4 := h3 t n
  rw [Bd_congr ρ (show c * c ^ (([Γ, e2'] ++ post).length + 1) = c ^ (post.length + 4) by
      simp only [List.length_append, List.length_cons, List.length_nil]; ring)
    (show 0 + ([Γ, e2'] ++ post).length + 1 = post.length + 3 by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)] at h4
  exact h4

theorem one_pair_D {κ : Type*} (Sw : Finset κ) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (Fw : κ → RK) (Γ e1' e2' : RK)
    (hFw : ∀ w, RNN (Fw w))
    (hΓ : RNN Γ ∧ RLE Γ (Bd c 0 ρ))
    (he1' : RNN e1' ∧ RLE e1' (Bd c 0 ρ)) (he2' : RNN e2' ∧ RLE e2' (Bd c 0 ρ))
    (pw : ∀ t1 t2 a n, ∑ w ∈ Sw, Fw w t1 a * Fw w t2 n ≤ e1' t1 a * e2' t2 n) (t n : ℕ) :
    ∑ w ∈ Sw, cv (Fw w) (cv Γ (Fw w)) t n ≤ Bd (c ^ 3) 2 ρ t n := by
  have hle := collapse Sw Fw Fw e1' e2' pw hFw [Γ] (by simpa using hΓ.1) t n
  refine hle.trans ?_
  have h1 : ∀ m ∈ [Γ], RNN m ∧ RLE m (Bd c 0 ρ) := by
    intro m hm
    simp only [List.mem_singleton] at hm
    subst hm; exact hΓ
  have h2 := chainL_Bd hρ hc [Γ] e2' h1 he2'.1 he2'.2
  have h3 := cv_Bd hρ he1'.1 (chainL_nonneg _ e2' (fun m hm => (h1 m hm).1) he2'.1) he1'.2 h2
  have h4 := h3 t n
  rw [Bd_congr ρ (show c * c ^ (([Γ] : List RK).length + 1) = c ^ 3 by
      simp only [List.length_cons, List.length_nil]; ring)
    (show 0 + ([Γ] : List RK).length + 1 = 2 by simp)] at h4
  exact h4

/-! ### Frobenius norms and the pair bounds -/

section Fro

open scoped Matrix.Norms.Frobenius

lemma fro_sq (A : Mt L) : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp [Real.rpow_two]
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

lemma fro_entry_le (A : Mt L) (i j : Fin L.Dm) : ‖A i j‖ ≤ ‖A‖ := by
  have h : ‖A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [fro_sq]
    calc ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact le_of_sq_le_sq h (norm_nonneg _)

lemma fro_le_of_entries (A : Mt L) (M : ℝ) (hM : 0 ≤ M) (h : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A‖ ≤ L.Dm * M := by
  have h2 : ‖A‖ ^ 2 ≤ ((L.Dm : ℝ) * M) ^ 2 := by
    rw [fro_sq]
    calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin L.Dm, ∑ _j : Fin L.Dm, M ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
      _ = ((L.Dm : ℝ) * M) ^ 2 := by simp; ring
  exact le_of_sq_le_sq h2 (by positivity)

lemma fro_trace (A : Mt L) : ‖A.trace‖ ≤ L.Dm * ‖A‖ := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖A.diag i‖ ≤ ∑ _i : Fin L.Dm, ‖A‖ :=
        Finset.sum_le_sum fun i _ => fro_entry_le L A i i
    _ = L.Dm * ‖A‖ := by simp

lemma fro_cv (F G : ℕ → ℕ → Mt L) (t n : ℕ) :
    ‖cv F G t n‖ ≤ cv (fun t n => ‖F t n‖) (fun t n => ‖G t n‖) t n := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  exact norm_mul_le _ _

lemma fro_chainL : ∀ (ms : List (ℕ → ℕ → Mt L)) (q : ℕ → ℕ → Mt L) (t n : ℕ),
    ‖chainL ms q t n‖ ≤ chainL (ms.map fun m => fun t n => ‖m t n‖) (fun t n => ‖q t n‖) t n
  | [], q, t, n => le_rfl
  | m :: ms, q, t, n => by
    refine (fro_cv L _ _ t n).trans ?_
    refine cv_mono (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => le_rfl) ?_ t n
    intro t n
    exact fro_chainL ms q t n

variable {L}

/-- real kernel of Frobenius norms -/
def NF (L : Lin d) (u : FreeGroup (Fin d)) : RK := fun t n => ‖Fr L t n u‖

def NG (L : Lin d) : RK := fun t n => ‖Gam L t n‖

theorem fro_Fr {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t n : ℕ) (u : FreeGroup (Fin d)) :
    ‖Fr L t n u‖ ≤ L.Dm * ρ ^ n :=
  fro_le_of_entries L _ _ (pow_nonneg ((norm_nonneg _).trans (hρ 0)) n)
    (fun x y => Fr_entry_le L ρ hρ t n u x y)

theorem fro_Gam {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t n : ℕ) :
    ‖Gam L t n‖ ≤ L.Dm * ρ ^ n :=
  fro_le_of_entries L _ _ (pow_nonneg ((norm_nonneg _).trans (hρ 0)) n)
    (fun x y => Gam_entry_le L ρ hρ t n x y)

theorem fro_Fr_bessel {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (t n : ℕ) (S : Finset (FreeGroup (Fin d))) :
    ∑ u ∈ S, ‖Fr L t n u‖ ^ 2 ≤ L.Dm * ρ ^ (2 * n) := by
  have h1 : ∀ u, ‖Fr L t n u‖ ^ 2 = ∑ x, ∑ y, ‖Fr L t n u x y‖ ^ 2 := fun u => fro_sq L _
  simp_rw [h1]
  calc ∑ u ∈ S, ∑ x, ∑ y, ‖Fr L t n u x y‖ ^ 2
      = ∑ x, ∑ u ∈ S, ∑ y, ‖Fr L t n u x y‖ ^ 2 := Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ u ∈ S, ‖Fr L t n u x y‖ ^ 2 :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ u ∈ S, ‖Fr L t n u x y‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ _y : Fin L.Dm, ρ ^ (2 * n) := Finset.sum_le_sum fun y _ => by
        exact Fr_bessel L ρ hρ t n S y
    _ = L.Dm * ρ ^ (2 * n) := by simp

theorem cs_pair {ι : Type*} (S : Finset ι) (f g : ι → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∑ i ∈ S, f i ^ 2 ≤ A ^ 2) (hg : ∑ i ∈ S, g i ^ 2 ≤ B ^ 2) :
    ∑ i ∈ S, f i * g i ≤ A * B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S f g
  have h2 : (∑ i ∈ S, f i * g i) ^ 2 ≤ (A * B) ^ 2 := by
    refine h.trans ?_
    rw [mul_pow]
    exact mul_le_mul hf hg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  exact le_of_sq_le_sq h2 (mul_nonneg hA hB)

theorem pair_Fr {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (S : Finset (FreeGroup (Fin d)))
    (t1 t2 a c : ℕ) :
    ∑ u ∈ S, ‖Fr L t1 a u‖ * ‖Fr L t2 c u‖ ≤ (L.Dm * ρ ^ a) * ρ ^ c := by
  have h0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
  have hD : (0 : ℝ) ≤ L.Dm := Nat.cast_nonneg _
  have := cs_pair S (fun u => ‖Fr L t1 a u‖) (fun u => ‖Fr L t2 c u‖)
    (A := Real.sqrt L.Dm * ρ ^ a) (B := Real.sqrt L.Dm * ρ ^ c) (by positivity) (by positivity)
    (by
      refine (fro_Fr_bessel hρ t1 a S).trans (le_of_eq ?_)
      rw [mul_pow, Real.sq_sqrt hD, ← pow_mul, mul_comm a 2])
    (by
      refine (fro_Fr_bessel hρ t2 c S).trans (le_of_eq ?_)
      rw [mul_pow, Real.sq_sqrt hD, ← pow_mul, mul_comm c 2])
  refine this.trans (le_of_eq ?_)
  have : Real.sqrt L.Dm * Real.sqrt L.Dm = L.Dm := Real.mul_self_sqrt hD
  calc Real.sqrt L.Dm * ρ ^ a * (Real.sqrt L.Dm * ρ ^ c)
      = (Real.sqrt L.Dm * Real.sqrt L.Dm) * ρ ^ a * ρ ^ c := by ring
    _ = (L.Dm * ρ ^ a) * ρ ^ c := by rw [this]

theorem pair_Fr_inv {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (S : Finset (FreeGroup (Fin d)))
    (t1 t2 a c : ℕ) :
    ∑ u ∈ S, ‖Fr L t1 a u‖ * ‖Fr L t2 c u⁻¹‖ ≤ (L.Dm * ρ ^ a) * ρ ^ c := by
  have h0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
  have hD : (0 : ℝ) ≤ L.Dm := Nat.cast_nonneg _
  have himg : ∑ u ∈ S, ‖Fr L t2 c u⁻¹‖ ^ 2 = ∑ u ∈ S.image (fun u => u⁻¹), ‖Fr L t2 c u‖ ^ 2 := by
    rw [Finset.sum_image]
    intro x _ y _ h
    exact inv_injective h
  have := cs_pair S (fun u => ‖Fr L t1 a u‖) (fun u => ‖Fr L t2 c u⁻¹‖)
    (A := Real.sqrt L.Dm * ρ ^ a) (B := Real.sqrt L.Dm * ρ ^ c) (by positivity) (by positivity)
    (by
      refine (fro_Fr_bessel hρ t1 a S).trans (le_of_eq ?_)
      rw [mul_pow, Real.sq_sqrt hD, ← pow_mul, mul_comm a 2])
    (by
      rw [himg]
      refine (fro_Fr_bessel hρ t2 c _).trans (le_of_eq ?_)
      rw [mul_pow, Real.sq_sqrt hD, ← pow_mul, mul_comm c 2])
  refine this.trans (le_of_eq ?_)
  have : Real.sqrt L.Dm * Real.sqrt L.Dm = L.Dm := Real.mul_self_sqrt hD
  calc Real.sqrt L.Dm * ρ ^ a * (Real.sqrt L.Dm * ρ ^ c)
      = (Real.sqrt L.Dm * Real.sqrt L.Dm) * ρ ^ a * ρ ^ c := by ring
    _ = (L.Dm * ρ ^ a) * ρ ^ c := by rw [this]

end Fro

theorem forall2_refl_nn : ∀ (l : List RK), (∀ m ∈ l, RNN m) →
    List.Forall₂ (fun a b => RNN a ∧ RLE a b) l l
  | [], _ => List.Forall₂.nil
  | m :: l, h => List.Forall₂.cons ⟨h m (by simp), fun _ _ => le_rfl⟩
      (forall2_refl_nn l (fun m' hm' => h m' (by simp [hm'])))

theorem two_pair_w {ι κ : Type*} (Sg : Finset ι) (Sw : Finset κ) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (Fg Fg' : ι → RK) (Fw : κ → RK) (Γ e1 e2 e1' e2' : RK) (post : κ → List RK) (postb : List RK)
    (hFg : ∀ g, RNN (Fg g)) (hFg' : ∀ g, RNN (Fg' g)) (hFw : ∀ w, RNN (Fw w))
    (hΓ : RNN Γ ∧ RLE Γ (Bd c 0 ρ))
    (hpw : ∀ w ∈ Sw, List.Forall₂ (fun a b => RNN a ∧ RLE a b) (post w) postb)
    (hpostb : ∀ m ∈ postb, RNN m ∧ RLE m (Bd c 0 ρ))
    (he1 : RNN e1 ∧ RLE e1 (Bd c 0 ρ)) (he2 : RNN e2 ∧ RLE e2 (Bd c 0 ρ))
    (he1' : RNN e1' ∧ RLE e1' (Bd c 0 ρ)) (he2' : RNN e2' ∧ RLE e2' (Bd c 0 ρ))
    (pg : ∀ t1 t2 a n, ∑ g ∈ Sg, Fg g t1 a * Fg' g t2 n ≤ e1 t1 a * e2 t2 n)
    (pw : ∀ t1 t2 a n, ∑ w ∈ Sw, Fw w t1 a * Fw w t2 n ≤ e1' t1 a * e2' t2 n) (t n : ℕ) :
    ∑ g ∈ Sg, ∑ w ∈ Sw, cv (Fg g) (chainL ([Γ, Fw w, Γ, Fw w] ++ post w) (Fg' g)) t n ≤
      Bd (c ^ (postb.length + 6)) (postb.length + 5) ρ t n := by
  refine le_trans (Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun w hw => ?_)
    (two_pair Sg Sw hρ hc Fg Fg' Fw Γ e1 e2 e1' e2' postb hFg hFw hΓ hpostb he1 he2 he1' he2' pg pw
      t n)
  have hA : List.Forall₂ (fun a b => RNN a ∧ RLE a b) [Γ, Fw w, Γ, Fw w] [Γ, Fw w, Γ, Fw w] :=
    forall2_refl_nn _ (by
      intro m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact hΓ.1
      · exact hFw w
      · exact hΓ.1
      · exact hFw w)
  have hF := List.rel_append hA (hpw w hw)
  obtain ⟨h1, h2⟩ := chainL_mono _ _ (Fg' g) (Fg' g) hF (hFg' g) (fun _ _ => le_rfl)
  exact cv_mono (hFg g) h1 (fun _ _ => le_rfl) h2 t n

theorem one_pair_w {κ : Type*} (Sw : Finset κ) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (Fw : κ → RK) (Γ e1' e2' : RK) (q : κ → RK) (qb : RK) (post : List RK)
    (hFw : ∀ w, RNN (Fw w))
    (hΓ : RNN Γ ∧ RLE Γ (Bd c 0 ρ)) (hpost : ∀ m ∈ post, RNN m ∧ RLE m (Bd c 0 ρ))
    (hq : ∀ w ∈ Sw, RNN (q w) ∧ RLE (q w) qb) (hqb : RNN qb ∧ RLE qb (Bd c 0 ρ))
    (he1' : RNN e1' ∧ RLE e1' (Bd c 0 ρ)) (he2' : RNN e2' ∧ RLE e2' (Bd c 0 ρ))
    (pw : ∀ t1 t2 a n, ∑ w ∈ Sw, Fw w t1 a * Fw w t2 n ≤ e1' t1 a * e2' t2 n) (t n : ℕ) :
    ∑ w ∈ Sw, cv (Fw w) (chainL ([Γ, Fw w] ++ post) (q w)) t n ≤
      Bd (c ^ (post.length + 4)) (post.length + 3) ρ t n := by
  refine le_trans (Finset.sum_le_sum fun w hw => ?_)
    (one_pair Sw hρ hc Fw Γ e1' e2' qb post hFw hΓ hpost hqb he1' he2' pw t n)
  have hA : List.Forall₂ (fun a b => RNN a ∧ RLE a b) ([Γ, Fw w] ++ post) ([Γ, Fw w] ++ post) :=
    forall2_refl_nn _ (by
      intro m hm
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hm
      rcases hm with rfl | rfl | h
      · exact hΓ.1
      · exact hFw w
      · exact (hpost m h).1)
  obtain ⟨h1, h2⟩ := chainL_mono _ _ (q w) qb hA (hq w hw).1 (hq w hw).2
  exact cv_mono (hFw w) h1 (fun _ _ => le_rfl) h2 t n

/-! ### Bridge to the sum over words -/

theorem Om_eq_sum : ∀ (n t : ℕ) (φ : List (Letter d) → ℂ),
    Om L t n φ = ∑ i : Fin n → Letter d, φ (List.ofFn i) •
      (List.ofFn fun j : Fin n => L.B (t + (j : ℕ)) (i j)).prod
  | 0, t, φ => by simp [Om]
  | n + 1, t, φ => by
    rw [Om_succ]
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Letter d))
      (fun p => φ (List.ofFn (Fin.consEquiv (fun _ : Fin (n + 1) => Letter d) p)) •
        (List.ofFn fun j : Fin (n + 1) => L.B (t + (j : ℕ))
          ((Fin.consEquiv (fun _ : Fin (n + 1) => Letter d) p) j)).prod) _ (fun p => rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Om_eq_sum n (t + 1) (fun w => φ (a :: w)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
      Fin.val_succ, add_zero, List.prod_cons]
    rw [mul_smul_comm]
    simp only [show ∀ j : ℕ, t + 1 + j = t + (j + 1) from fun j => by omega]

/-! ### The four shapes -/

section Shapes

open scoped Matrix.Norms.Frobenius

variable {L}

def postK (L : Lin d) (j : ℕ) (w : FreeGroup (Fin d)) : List RK :=
  (if j = 0 then [] else [NG L, NF L (w ^ j)]) ++ [NG L]

def TTA (L : Lin d) (j : ℕ) (g w : FreeGroup (Fin d)) : RK :=
  cv (NF L g) (chainL ([NG L, NF L w, NG L, NF L w] ++ postK L j w) (NF L g⁻¹))

theorem mk_flatten' {d : ℕ} (c : List (Fin d × Bool)) (k : ℕ) :
    FreeGroup.mk (List.replicate k c).flatten = (FreeGroup.mk c) ^ k := by
  induction k with
  | zero => simp; rfl
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, ← FreeGroup.mul_mk, ih, pow_succ']

theorem A_u (j : ℕ) (u : FreeGroup (Fin d)) (c0 cy : List (Fin d × Bool)) (h0 : c0 ≠ [])
    (h1 : cy ≠ [])
    (hform : u.toWord = c0 ++ (List.replicate (j + 2) cy).flatten ++ FreeGroup.invRev c0)
    (t n : ℕ) :
    ‖Fr L t n u‖ ≤ TTA L j (FreeGroup.mk c0) (FreeGroup.mk cy) t n := by
  set Kb : List (List (Fin d × Bool)) :=
    if j = 0 then [] else [(List.replicate j cy).flatten] with hKb
  set Bs : List (List (Fin d × Bool)) := [cy, cy] ++ Kb ++ [FreeGroup.invRev c0] with hBs
  have hflat : Bs.flatten = (List.replicate (j + 2) cy).flatten ++ FreeGroup.invRev c0 := by
    by_cases hj : j = 0
    · subst hj; simp [hBs, hKb]
    · simp only [hBs, hKb, hj, if_false, List.cons_append, List.nil_append, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.replicate_succ, List.flatten_cons]
      simp
  have hne : ∀ B ∈ Bs, B ≠ [] := by
    intro B hB
    simp only [hBs, hKb] at hB
    by_cases hj : j = 0
    · simp only [hj, if_true, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl | rfl
      · exact h1
      · exact h1
      · intro h
        apply h0
        have := congrArg List.length h
        simpa using this
    · simp only [hj, if_false, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false, List.append_nil, List.mem_singleton] at hB
      rcases hB with rfl | rfl | rfl | rfl
      · exact h1
      · exact h1
      · intro h
        have := congrArg List.length h
        simp only [List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul,
          List.length_nil] at this
        have hl : 0 < cy.length := List.length_pos_iff.mpr h1
        have : j * cy.length = 0 := this
        rcases Nat.mul_eq_zero.mp this with h | h
        · exact hj h
        · omega
      · intro h
        apply h0
        have := congrArg List.length h
        simpa using this
  have hred : FreeGroup.IsReduced (c0 ++ Bs.flatten) := by
    rw [hflat, ← List.append_assoc, ← hform]; exact FreeGroup.isReduced_toWord
  have hu : FreeGroup.mk (c0 ++ Bs.flatten) = u := by
    rw [hflat, ← List.append_assoc, ← hform]; exact FreeGroup.mk_toWord
  have hchain := Fr_chain L c0 Bs hne hred
  rw [hu] at hchain
  have hbl : blockList L Bs =
      ([Gam L, FrK L (FreeGroup.mk cy), Gam L, FrK L (FreeGroup.mk cy)] ++
        ((if j = 0 then [] else [Gam L, FrK L (FreeGroup.mk (List.replicate j cy).flatten)]) ++
          [Gam L])) ++ [FrK L (FreeGroup.mk (FreeGroup.invRev c0))] := by
    by_cases hj : j = 0 <;> simp [blockList, hBs, hKb, hj]
  rw [hbl, chainR_eq_chainL] at hchain
  have e1 : FrK L u t n = Fr L t n u := rfl
  rw [← e1, show FrK L u = _ from hchain]
  refine (fro_cv L _ _ t n).trans ?_
  have hmap : (([Gam L, FrK L (FreeGroup.mk cy), Gam L, FrK L (FreeGroup.mk cy)] ++
        ((if j = 0 then [] else [Gam L, FrK L (FreeGroup.mk (List.replicate j cy).flatten)]) ++
          [Gam L])).map fun m => fun t n => ‖m t n‖) =
      [NG L, NF L (FreeGroup.mk cy), NG L, NF L (FreeGroup.mk cy)] ++
        postK L j (FreeGroup.mk cy) := by
    by_cases hj : j = 0
    · simp only [postK, hj, if_true, List.map_append, List.map_cons, List.map_nil, List.append_nil,
        List.nil_append]
      rfl
    · simp only [postK, hj, if_false, List.map_append, List.map_cons, List.map_nil, mk_flatten']
      rfl
  have hq : (fun t n => ‖FrK L (FreeGroup.mk (FreeGroup.invRev c0)) t n‖) =
      NF L (FreeGroup.mk c0)⁻¹ := by
    funext t n
    simp [NF, FrK, FreeGroup.inv_mk]
  refine cv_mono (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => le_rfl) ?_ t n
  intro t n
  refine (fro_chainL L _ _ t n).trans (le_of_eq ?_)
  rw [hmap, hq]

lemma NG_bd {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) :
    RNN (NG L) ∧ RLE (NG L) (Bd (L.Dm : ℝ) 0 ρ) :=
  ⟨fun _ _ => norm_nonneg _, fun t n => by simpa [NG, Bd] using fro_Gam hρ t n⟩

lemma e1_bd {ρ : ℝ} (hρ0 : 0 ≤ ρ) :
    RNN (fun (_ a : ℕ) => (L.Dm : ℝ) * ρ ^ a) ∧
      RLE (fun (_ a : ℕ) => (L.Dm : ℝ) * ρ ^ a) (Bd (L.Dm : ℝ) 0 ρ) :=
  ⟨fun _ _ => by positivity, fun t n => by simp [Bd]⟩

lemma e2_bd {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hD1 : 1 ≤ L.Dm) :
    RNN (fun (_ c : ℕ) => ρ ^ c) ∧ RLE (fun (_ c : ℕ) => ρ ^ c) (Bd (L.Dm : ℝ) 0 ρ) := by
  refine ⟨fun _ _ => by positivity, fun t n => ?_⟩
  have : (1 : ℝ) ≤ L.Dm := by exact_mod_cast hD1
  simp only [Bd, pow_zero, mul_one]
  nlinarith [pow_nonneg hρ0 n]

lemma bd_final {c ρ : ℝ} (hc : 1 ≤ c) (hρ : 0 ≤ ρ) {r i : ℕ} (hr : r ≤ 9) (hi : i ≤ 8) (t m : ℕ) :
    Bd (c ^ r) i ρ t m ≤ c ^ 9 * ((m : ℝ) + 1) ^ 8 * ρ ^ m := by
  simp only [Bd]
  have h1 : c ^ r ≤ c ^ 9 := pow_le_pow_right₀ hc hr
  have h2 : ((m : ℝ) + 1) ^ i ≤ ((m : ℝ) + 1) ^ 8 :=
    pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]) hi
  have h3 : 0 ≤ ρ ^ m := pow_nonneg hρ m
  have h4 : 0 ≤ c ^ r := by positivity
  have h5 : 0 ≤ ((m : ℝ) + 1) ^ i := by positivity
  calc c ^ r * ((m : ℝ) + 1) ^ i * ρ ^ m ≤ c ^ 9 * ((m : ℝ) + 1) ^ 8 * ρ ^ m := by
        gcongr

theorem u_eq_conj (j : ℕ) (u : FreeGroup (Fin d)) (c0 cy : List (Fin d × Bool))
    (hform : u.toWord = c0 ++ (List.replicate (j + 2) cy).flatten ++ FreeGroup.invRev c0) :
    u = FreeGroup.mk c0 * (FreeGroup.mk cy) ^ (j + 2) * (FreeGroup.mk c0)⁻¹ := by
  have := congrArg FreeGroup.mk hform
  rw [FreeGroup.mk_toWord, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, mk_flatten',
    ← FreeGroup.inv_mk] at this
  exact this

lemma postK_nn (j : ℕ) (w : FreeGroup (Fin d)) : ∀ m ∈ postK L j w, RNN m := by
  intro m hm
  by_cases hj : j = 0
  · simp only [postK, hj, if_true, List.nil_append, List.mem_singleton] at hm
    subst hm; exact fun _ _ => norm_nonneg _
  · simp only [postK, hj, if_false, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> exact fun _ _ => norm_nonneg _

theorem shapeA {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (hD1 : 1 ≤ L.Dm) (j m : ℕ)
    (S : Finset (FreeGroup (Fin d))) (c0 cy : FreeGroup (Fin d) → List (Fin d × Bool))
    (h0 : ∀ u ∈ S, c0 u ≠ []) (h1 : ∀ u ∈ S, cy u ≠ [])
    (hform : ∀ u ∈ S, u.toWord =
      c0 u ++ (List.replicate (j + 2) (cy u)).flatten ++ FreeGroup.invRev (c0 u)) :
    ∑ u ∈ S, ‖Fr L 1 m u‖ ≤ (L.Dm : ℝ) ^ 9 * ((m : ℝ) + 1) ^ 8 * ρ ^ m := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
  have hDr : (1 : ℝ) ≤ L.Dm := by exact_mod_cast hD1
  set φ : FreeGroup (Fin d) → FreeGroup (Fin d) × FreeGroup (Fin d) :=
    fun u => (FreeGroup.mk (c0 u), FreeGroup.mk (cy u)) with hφ
  have hTT : ∀ g w, RNN (TTA L j g w) := by
    intro g w
    refine cv_nonneg (fun _ _ => norm_nonneg _) (chainL_nonneg _ _ ?_ (fun _ _ => norm_nonneg _))
    intro m' hm'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hm'
    rcases hm' with rfl | rfl | rfl | rfl | h
    · exact fun _ _ => norm_nonneg _
    · exact fun _ _ => norm_nonneg _
    · exact fun _ _ => norm_nonneg _
    · exact fun _ _ => norm_nonneg _
    · exact postK_nn j w m' h
  have hstep1 : ∑ u ∈ S, ‖Fr L 1 m u‖ ≤ ∑ u ∈ S, TTA L j (φ u).1 (φ u).2 1 m :=
    Finset.sum_le_sum fun u hu => A_u j u (c0 u) (cy u) (h0 u hu) (h1 u hu) (hform u hu) 1 m
  have hinj : Set.InjOn φ S := by
    intro u hu u' hu' h
    have e1 := u_eq_conj j u (c0 u) (cy u) (hform u hu)
    have e2 := u_eq_conj j u' (c0 u') (cy u') (hform u' hu')
    have hg : FreeGroup.mk (c0 u) = FreeGroup.mk (c0 u') := congrArg Prod.fst h
    have hw : FreeGroup.mk (cy u) = FreeGroup.mk (cy u') := congrArg Prod.snd h
    rw [e1, e2, hg, hw]
  set Sg := S.image (fun u => (φ u).1) with hSg
  set Sw := S.image (fun u => (φ u).2) with hSw
  have hstep2 : ∑ u ∈ S, TTA L j (φ u).1 (φ u).2 1 m ≤
      ∑ g ∈ Sg, ∑ w ∈ Sw, TTA L j g w 1 m := by
    rw [← Finset.sum_product (f := fun x : FreeGroup (Fin d) × FreeGroup (Fin d) =>
      TTA L j x.1 x.2 1 m)]
    rw [← Finset.sum_image (f := fun x : FreeGroup (Fin d) × FreeGroup (Fin d) =>
      TTA L j x.1 x.2 1 m) (s := S) (g := φ) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => hTT _ _ _ _)
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hu, Finset.mem_image_of_mem _ hu⟩
  set kbK : RK := fun _ n => (L.Dm : ℝ) * ρ ^ n with hkb
  set postb : List RK := (if j = 0 then [] else [NG L, kbK]) ++ [NG L] with hpostb
  have hmain := two_pair_w Sg Sw hρ0 (by linarith : (0 : ℝ) ≤ L.Dm)
    (fun g => NF L g) (fun g => NF L g⁻¹) (fun w => NF L w) (NG L)
    (fun _ a => (L.Dm : ℝ) * ρ ^ a) (fun _ c => ρ ^ c) (fun _ a => (L.Dm : ℝ) * ρ ^ a)
    (fun _ c => ρ ^ c) (postK L j) postb (fun _ _ _ => norm_nonneg _) (fun _ _ _ => norm_nonneg _)
    (fun _ _ _ => norm_nonneg _) (NG_bd hρ)
    (by
      intro w _
      by_cases hj : j = 0
      · simp only [postK, hpostb, hj, if_true, List.nil_append]
        exact forall2_refl_nn _ (by
          intro m' hm'; simp only [List.mem_singleton] at hm'; subst hm'; exact fun _ _ => norm_nonneg _)
      · simp only [postK, hpostb, hj, if_false]
        refine List.Forall₂.cons ⟨fun _ _ => norm_nonneg _, fun _ _ => le_rfl⟩
          (List.Forall₂.cons ⟨fun _ _ => norm_nonneg _, fun t n => ?_⟩
            (List.Forall₂.cons ⟨fun _ _ => norm_nonneg _, fun _ _ => le_rfl⟩ List.Forall₂.nil))
        exact fro_Fr hρ t n _)
    (by
      intro m' hm'
      by_cases hj : j = 0
      · simp only [hpostb, hj, if_true, List.nil_append, List.mem_singleton] at hm'
        subst hm'; exact NG_bd hρ
      · simp only [hpostb, hj, if_false, List.cons_append, List.nil_append, List.mem_cons,
          List.mem_singleton, List.not_mem_nil, or_false] at hm'
        rcases hm' with rfl | rfl | rfl
        · exact NG_bd hρ
        · exact e1_bd hρ0
        · exact NG_bd hρ)
    (e1_bd hρ0) (e2_bd hρ0 hD1) (e1_bd hρ0) (e2_bd hρ0 hD1)
    (fun t1 t2 a n => pair_Fr_inv hρ Sg t1 t2 a n) (fun t1 t2 a n => pair_Fr hρ Sw t1 t2 a n) 1 m
  refine hstep1.trans (hstep2.trans (hmain.trans ?_))
  have hlen : postb.length = 1 ∨ postb.length = 3 := by
    by_cases hj : j = 0
    · left; simp [hpostb, hj]
    · right; simp [hpostb, hj]
  rcases hlen with h | h
  · rw [h]; exact bd_final hDr hρ0 (by omega) (by omega) 1 m
  · rw [h]; exact bd_final hDr hρ0 (by omega) (by omega) 1 m

def TTC (L : Lin d) (j : ℕ) (w : FreeGroup (Fin d)) : RK :=
  cv (NF L w) (chainL [NG L, NF L w, NG L] (NF L (w ^ j)))

def TTD (L : Lin d) (w : FreeGroup (Fin d)) : RK :=
  cv (NF L w) (chainL [NG L] (NF L w))

theorem C_u3 (j : ℕ) (hj : 1 ≤ j) (u : FreeGroup (Fin d)) (cy : List (Fin d × Bool))
    (h1 : cy ≠ []) (hform : u.toWord = (List.replicate (j + 2) cy).flatten) (t n : ℕ) :
    ‖Fr L t n u‖ ≤ TTC L j (FreeGroup.mk cy) t n := by
  set K := (List.replicate j cy).flatten with hK
  have hKne : K ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [hK, List.length_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul,
      List.length_nil] at this
    have hl : 0 < cy.length := List.length_pos_iff.mpr h1
    rcases Nat.mul_eq_zero.mp this with h | h <;> omega
  set Bs : List (List (Fin d × Bool)) := [cy, K] with hBs
  have hflat : cy ++ Bs.flatten = (List.replicate (j + 2) cy).flatten := by
    simp [hBs, hK, List.replicate_succ]
  have hne : ∀ B ∈ Bs, B ≠ [] := by
    intro B hB
    simp only [hBs, List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    · exact h1
    · exact hKne
  have hred : FreeGroup.IsReduced (cy ++ Bs.flatten) := by
    rw [hflat, ← hform]; exact FreeGroup.isReduced_toWord
  have hu : FreeGroup.mk (cy ++ Bs.flatten) = u := by
    rw [hflat, ← hform]; exact FreeGroup.mk_toWord
  have hchain := Fr_chain L cy Bs hne hred
  rw [hu] at hchain
  have hbl : blockList L Bs = [Gam L, FrK L (FreeGroup.mk cy), Gam L] ++ [FrK L (FreeGroup.mk K)] := by
    simp [blockList, hBs]
  rw [hbl, chainR_eq_chainL] at hchain
  have e1 : FrK L u t n = Fr L t n u := rfl
  rw [← e1, show FrK L u = _ from hchain]
  refine (fro_cv L _ _ t n).trans ?_
  have hq : (fun t n => ‖FrK L (FreeGroup.mk K) t n‖) = NF L ((FreeGroup.mk cy) ^ j) := by
    funext t n
    simp only [NF, FrK, hK, mk_flatten']
  refine cv_mono (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => le_rfl) ?_ t n
  intro t n
  refine (fro_chainL L _ _ t n).trans (le_of_eq ?_)
  rw [hq]
  rfl

theorem C_u2 (u : FreeGroup (Fin d)) (cy : List (Fin d × Bool))
    (h1 : cy ≠ []) (hform : u.toWord = (List.replicate (0 + 2) cy).flatten) (t n : ℕ) :
    ‖Fr L t n u‖ ≤ TTD L (FreeGroup.mk cy) t n := by
  set Bs : List (List (Fin d × Bool)) := [cy] with hBs
  have hflat : cy ++ Bs.flatten = (List.replicate (0 + 2) cy).flatten := by
    simp [hBs, List.replicate_succ]
  have hne : ∀ B ∈ Bs, B ≠ [] := by
    intro B hB
    simp only [hBs, List.mem_singleton] at hB
    subst hB; exact h1
  have hred : FreeGroup.IsReduced (cy ++ Bs.flatten) := by
    rw [hflat, ← hform]; exact FreeGroup.isReduced_toWord
  have hu : FreeGroup.mk (cy ++ Bs.flatten) = u := by
    rw [hflat, ← hform]; exact FreeGroup.mk_toWord
  have hchain := Fr_chain L cy Bs hne hred
  rw [hu] at hchain
  have hbl : blockList L Bs = [Gam L] ++ [FrK L (FreeGroup.mk cy)] := by
    simp [blockList, hBs]
  rw [hbl, chainR_eq_chainL] at hchain
  have e1 : FrK L u t n = Fr L t n u := rfl
  rw [← e1, show FrK L u = _ from hchain]
  refine (fro_cv L _ _ t n).trans ?_
  refine cv_mono (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) (fun _ _ => le_rfl) ?_ t n
  intro t n
  refine (fro_chainL L _ _ t n).trans (le_of_eq ?_)
  rfl

theorem u_eq_pow (j : ℕ) (u : FreeGroup (Fin d)) (cy : List (Fin d × Bool))
    (hform : u.toWord = (List.replicate (j + 2) cy).flatten) :
    u = (FreeGroup.mk cy) ^ (j + 2) := by
  have := congrArg FreeGroup.mk hform
  rw [FreeGroup.mk_toWord, mk_flatten'] at this
  exact this

theorem shapeC3 {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (hD1 : 1 ≤ L.Dm) (j m : ℕ) (hj : 1 ≤ j)
    (S : Finset (FreeGroup (Fin d))) (cy : FreeGroup (Fin d) → List (Fin d × Bool))
    (h1 : ∀ u ∈ S, cy u ≠ [])
    (hform : ∀ u ∈ S, u.toWord = (List.replicate (j + 2) (cy u)).flatten) :
    ∑ u ∈ S, ‖Fr L 1 m u‖ ≤ (L.Dm : ℝ) ^ 9 * ((m : ℝ) + 1) ^ 8 * ρ ^ m := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
  have hDr : (1 : ℝ) ≤ L.Dm := by exact_mod_cast hD1
  set φ : FreeGroup (Fin d) → FreeGroup (Fin d) := fun u => FreeGroup.mk (cy u) with hφ
  have hTT : ∀ w, RNN (TTC L j w) := by
    intro w
    refine cv_nonneg (fun _ _ => norm_nonneg _) (chainL_nonneg _ _ ?_ (fun _ _ => norm_nonneg _))
    intro m' hm'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
    rcases hm' with rfl | rfl | rfl <;> exact fun _ _ => norm_nonneg _
  have hstep1 : ∑ u ∈ S, ‖Fr L 1 m u‖ ≤ ∑ u ∈ S, TTC L j (φ u) 1 m :=
    Finset.sum_le_sum fun u hu => C_u3 j hj u (cy u) (h1 u hu) (hform u hu) 1 m
  have hinj : Set.InjOn φ S := by
    intro u hu u' hu' h
    rw [u_eq_pow j u (cy u) (hform u hu), u_eq_pow j u' (cy u') (hform u' hu')]
    exact congrArg (· ^ (j + 2)) h
  set Sw := S.image φ with hSw
  have hstep2 : ∑ u ∈ S, TTC L j (φ u) 1 m ≤ ∑ w ∈ Sw, TTC L j w 1 m := by
    rw [Finset.sum_image hinj]
  set kbK : RK := fun _ n => (L.Dm : ℝ) * ρ ^ n with hkb
  have hmain := one_pair_w Sw hρ0 (by linarith : (0 : ℝ) ≤ L.Dm) (fun w => NF L w) (NG L)
    (fun _ a => (L.Dm : ℝ) * ρ ^ a) (fun _ c => ρ ^ c) (fun w => NF L (w ^ j)) kbK [NG L]
    (fun _ _ _ => norm_nonneg _) (NG_bd hρ)
    (by
      intro m' hm'
      simp only [List.mem_singleton] at hm'
      subst hm'; exact NG_bd hρ)
    (fun w _ => ⟨fun _ _ => norm_nonneg _, fun t n => fro_Fr hρ t n _⟩) (e1_bd hρ0)
    (e1_bd hρ0) (e2_bd hρ0 hD1) (fun t1 t2 a n => pair_Fr hρ Sw t1 t2 a n) 1 m
  refine hstep1.trans (hstep2.trans (le_trans (le_of_eq ?_) (hmain.trans ?_)))
  · rfl
  · exact bd_final hDr hρ0 (by simp) (by simp) 1 m

theorem shapeC2 {ρ : ℝ} (hρ : ∀ j, ‖Xop L j‖ ≤ ρ) (hD1 : 1 ≤ L.Dm) (m : ℕ)
    (S : Finset (FreeGroup (Fin d))) (cy : FreeGroup (Fin d) → List (Fin d × Bool))
    (h1 : ∀ u ∈ S, cy u ≠ [])
    (hform : ∀ u ∈ S, u.toWord = (List.replicate (0 + 2) (cy u)).flatten) :
    ∑ u ∈ S, ‖Fr L 1 m u‖ ≤ (L.Dm : ℝ) ^ 9 * ((m : ℝ) + 1) ^ 8 * ρ ^ m := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans (hρ 0)
  have hDr : (1 : ℝ) ≤ L.Dm := by exact_mod_cast hD1
  set φ : FreeGroup (Fin d) → FreeGroup (Fin d) := fun u => FreeGroup.mk (cy u) with hφ
  have hstep1 : ∑ u ∈ S, ‖Fr L 1 m u‖ ≤ ∑ u ∈ S, TTD L (φ u) 1 m :=
    Finset.sum_le_sum fun u hu => C_u2 u (cy u) (h1 u hu) (hform u hu) 1 m
  have hinj : Set.InjOn φ S := by
    intro u hu u' hu' h
    rw [u_eq_pow 0 u (cy u) (hform u hu), u_eq_pow 0 u' (cy u') (hform u' hu')]
    exact congrArg (· ^ (0 + 2)) h
  set Sw := S.image φ with hSw
  have hTT : ∀ w, RNN (TTD L w) := by
    intro w
    refine cv_nonneg (fun _ _ => norm_nonneg _) (chainL_nonneg _ _ ?_ (fun _ _ => norm_nonneg _))
    intro m' hm'
    simp only [List.mem_singleton] at hm'
    subst hm'; exact fun _ _ => norm_nonneg _
  have hstep2 : ∑ u ∈ S, TTD L (φ u) 1 m ≤ ∑ w ∈ Sw, TTD L w 1 m := by
    rw [Finset.sum_image hinj]
  have hmain := one_pair_D Sw hρ0 (by linarith : (0 : ℝ) ≤ L.Dm) (fun w => NF L w) (NG L)
    (fun _ a => (L.Dm : ℝ) * ρ ^ a) (fun _ c => ρ ^ c)
    (fun _ _ _ => norm_nonneg _) (NG_bd hρ) (e1_bd hρ0) (e2_bd hρ0 hD1)
    (fun t1 t2 a n => pair_Fr hρ Sw t1 t2 a n) 1 m
  refine hstep1.trans (hstep2.trans (le_trans (le_of_eq ?_) (hmain.trans ?_)))
  · rfl
  · exact bd_final hDr hρ0 (by norm_num) (by norm_num) 1 m

lemma Bprod_eq (m : ℕ) (i : Fin m → Letter d) :
    Bprod L m i = (List.ofFn fun j : Fin m => L.B (1 + (j : ℕ)) (i j)).prod := by
  unfold Bprod
  simp only [add_comm]

theorem cyc_ne_nil' {d : ℕ} (v : FreeGroup (Fin d)) (hv : v ≠ 1) :
    FreeGroup.reduceCyclically v.toWord ≠ [] := by
  intro h
  apply hv
  have := congr_arg FreeGroup.mk (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically v.toWord)
  rw [FreeGroup.mk_toWord, h, List.append_nil, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk,
    mul_inv_cancel] at this
  exact this.symm

theorem toWord_pow_eq' {d : ℕ} (v : FreeGroup (Fin d)) (m : ℕ) (hm : 1 ≤ m) :
    (v ^ m).toWord = FreeGroup.reduceCyclically.conjugator v.toWord ++
      (List.replicate m (FreeGroup.reduceCyclically v.toWord)).flatten ++
        FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator v.toWord) := by
  rw [FreeGroup.toWord_pow, FreeGroup.reduceCyclically.reduce_flatten_replicate
    FreeGroup.isReduced_toWord, if_neg (by omega)]


/-- `core_bound` with a bounded weight `G` on the reduced words: the proof bounds the sum of the
norms of the per-`u` terms, so any weight of modulus `≤ B` goes through. -/
theorem core_bound_w (L : Lin d) (D : ℕ) (hD : 1 ≤ D) (hDm : D ≤ L.Dm) (hS : L.Supp D)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ j, ‖Xop L j‖ ≤ R ^ (1 / (L.q : ℝ))) (p k : ℕ) (hp : 1 ≤ p)
    (hk : 2 ≤ k) (G : FreeGroup (Fin d) → ℂ) (B : ℝ) (hB0 : 0 ≤ B) (hG : ∀ u, ‖G u‖ ≤ B) :
    ‖∑ i : Fin (p * L.q) → Letter d, aCoef L D (p * L.q) i *
        (G (wordFree (List.ofFn i)) *
          (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ k
           then (1 : ℂ) else 0))‖ ≤
      B * (2 * (L.Dm : ℝ) ^ 12 * (((p * L.q : ℕ) : ℝ) + 1) ^ 12 * R ^ p) := by
  classical
  set m := p * L.q with hm
  set ρ : ℝ := R ^ (1 / (L.q : ℝ)) with hρdef
  have hρ : ∀ j, ‖Xop L j‖ ≤ ρ := hR
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg hR0 _
  have hρR : ρ ^ m = R ^ p := by
    have hq0 : (L.q : ℝ) ≠ 0 := by
      have := L.hq
      positivity
    rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul hR0]
    have : (1 / (L.q : ℝ)) * ((m : ℕ) : ℝ) = (p : ℝ) := by
      rw [hm]; push_cast; field_simp
    rw [this, Real.rpow_natCast]
  have hD1 : 1 ≤ L.Dm := hD.trans hDm
  have hDr : (1 : ℝ) ≤ L.Dm := by exact_mod_cast hD1
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  set W : (Fin m → Letter d) → FreeGroup (Fin d) := fun i => wordFree (List.ofFn i) with hW
  set U : Finset (FreeGroup (Fin d)) := (Finset.univ.image W).filter
    (fun u => ∃ v, IsNonPower v ∧ u = v ^ (j + 2)) with hU
  have hind : ∀ i : Fin m → Letter d, G (W i) * (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧
      wordFree (List.ofFn i) = v ^ (j + 2) then (1 : ℂ) else 0) =
      ∑ u ∈ U, G u * (if W i = u then (1 : ℂ) else 0) := by
    intro i
    have e : ∀ u ∈ U, G u * (if W i = u then (1 : ℂ) else 0) =
        if W i = u then G (W i) else 0 := by
      intro u _
      by_cases h : W i = u
      · rw [if_pos h, if_pos h, h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq]
    by_cases h : ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ (j + 2)
    · rw [if_pos h, if_pos, mul_one]
      simp only [hU, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨i, Finset.mem_univ _, rfl⟩, h⟩
    · rw [if_neg h, if_neg, mul_zero]
      intro hmem
      simp only [hU, Finset.mem_filter] at hmem
      exact h hmem.2
  have hsum : ∑ i : Fin m → Letter d, aCoef L D m i * (G (wordFree (List.ofFn i)) *
      (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧
      wordFree (List.ofFn i) = v ^ (j + 2) then (1 : ℂ) else 0)) =
      ∑ u ∈ U, G u * ((D : ℂ)⁻¹ * (Fr L 1 m u).trace) := by
    simp only [show ∀ i : Fin m → Letter d, wordFree (List.ofFn i) = W i from fun _ => rfl] at hind ⊢
    simp only [hind]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hFr : Fr L 1 m u = ∑ i : Fin m → Letter d,
        (if W i = u then (1 : ℂ) else 0) • Bprod L m i := by
      unfold Fr
      rw [Om_eq_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Bprod_eq]
    rw [hFr, Matrix.trace_sum]
    simp_rw [Matrix.trace_smul]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [aCoef, smul_eq_mul]
    ring
  rw [hsum]
  have hex : ∀ u ∈ U, ∃ v : FreeGroup (Fin d), IsNonPower v ∧ u = v ^ (j + 2) :=
    fun u hu => (Finset.mem_filter.mp hu).2
  choose! vOf hvnp hvu using hex
  set c0 : FreeGroup (Fin d) → List (Fin d × Bool) :=
    fun u => FreeGroup.reduceCyclically.conjugator (vOf u).toWord with hc0
  set cy : FreeGroup (Fin d) → List (Fin d × Bool) :=
    fun u => FreeGroup.reduceCyclically (vOf u).toWord with hcy_def
  have hcy : ∀ u ∈ U, cy u ≠ [] := fun u hu => cyc_ne_nil' _ (hvnp u hu).1
  have hform : ∀ u ∈ U, u.toWord =
      c0 u ++ (List.replicate (j + 2) (cy u)).flatten ++ FreeGroup.invRev (c0 u) := by
    intro u hu
    have := toWord_pow_eq' (vOf u) (j + 2) (by omega)
    rw [← hvu u hu] at this
    exact this
  set Bnd : ℝ := (L.Dm : ℝ) ^ 9 * ((m : ℝ) + 1) ^ 8 * ρ ^ m with hBnd
  have hA : ∑ u ∈ U.filter (fun u => c0 u ≠ []), ‖Fr L 1 m u‖ ≤ Bnd :=
    shapeA hρ hD1 j m _ c0 cy (fun u hu => (Finset.mem_filter.mp hu).2)
      (fun u hu => hcy u (Finset.mem_filter.mp hu).1)
      (fun u hu => hform u (Finset.mem_filter.mp hu).1)
  have hC : ∑ u ∈ U.filter (fun u => ¬ (c0 u ≠ [])), ‖Fr L 1 m u‖ ≤ Bnd := by
    have hform' : ∀ u ∈ U.filter (fun u => ¬ (c0 u ≠ [])),
        u.toWord = (List.replicate (j + 2) (cy u)).flatten := by
      intro u hu
      have h1 := hform u (Finset.mem_filter.mp hu).1
      have h0 : c0 u = [] := by simpa using (Finset.mem_filter.mp hu).2
      rw [h0] at h1
      simpa using h1
    have hcy' : ∀ u ∈ U.filter (fun u => ¬ (c0 u ≠ [])), cy u ≠ [] :=
      fun u hu => hcy u (Finset.mem_filter.mp hu).1
    by_cases hj : j = 0
    · subst hj
      exact shapeC2 hρ hD1 m _ cy hcy' hform'
    · exact shapeC3 hρ hD1 j m (Nat.one_le_iff_ne_zero.mpr hj) _ cy hcy' hform'
  have hsplit := Finset.sum_filter_add_sum_filter_not U (fun u => c0 u ≠ [])
    (fun u => ‖Fr L 1 m u‖)
  have hnorm : ‖∑ u ∈ U, G u * ((D : ℂ)⁻¹ * (Fr L 1 m u).trace)‖ ≤
      B * ((L.Dm : ℝ) * ∑ u ∈ U, ‖Fr L 1 m u‖) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    have hDinv : ‖(D : ℂ)⁻¹‖ ≤ 1 := by
      simp only [norm_inv, Complex.norm_natCast]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast hD)
    calc ‖G u * ((D : ℂ)⁻¹ * (Fr L 1 m u).trace)‖
        = ‖G u‖ * (‖(D : ℂ)⁻¹‖ * ‖(Fr L 1 m u).trace‖) := by rw [norm_mul, norm_mul]
      _ ≤ B * (1 * ‖(Fr L 1 m u).trace‖) := by
          exact mul_le_mul (hG u) (mul_le_mul_of_nonneg_right hDinv (norm_nonneg _)) (by positivity) hB0
      _ ≤ B * (L.Dm * ‖Fr L 1 m u‖) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left (fro_trace L _) hB0
  refine hnorm.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hB0
  rw [← hsplit]
  have hDm0 : (0 : ℝ) ≤ L.Dm := by linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hRp : 0 ≤ R ^ p := pow_nonneg hR0 p
  calc (L.Dm : ℝ) * (∑ u ∈ U.filter (fun u => c0 u ≠ []), ‖Fr L 1 m u‖ +
        ∑ u ∈ U.filter (fun u => ¬ (c0 u ≠ [])), ‖Fr L 1 m u‖)
      ≤ (L.Dm : ℝ) * (Bnd + Bnd) := by gcongr
    _ = 2 * (L.Dm : ℝ) ^ 10 * ((m : ℝ) + 1) ^ 8 * R ^ p := by rw [hBnd, hρR]; ring
    _ ≤ 2 * (L.Dm : ℝ) ^ 12 * ((m : ℝ) + 1) ^ 12 * R ^ p := by
        have h1 : (L.Dm : ℝ) ^ 10 ≤ (L.Dm : ℝ) ^ 12 := pow_le_pow_right₀ hDr (by norm_num)
        have h2 : ((m : ℝ) + 1) ^ 8 ≤ ((m : ℝ) + 1) ^ 12 := pow_le_pow_right₀ hm1 (by norm_num)
        have h3 : (0 : ℝ) ≤ (L.Dm : ℝ) ^ 10 := by positivity
        have h4 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ 8 := by positivity
        gcongr

end Shapes

end StrongConv.S9.PartCore

end
end
end

section
section
set_option autoImplicit true
open Polynomial Filter Topology

noncomputable section

open scoped Classical

namespace StrongConv.S9.PartCoreOne

open StrongConv StrongConv.S9 StrongConv.S9.PartLin
open scoped InnerProductSpace

lemma leftReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    leftReg g f h = f (g⁻¹ * h) := rfl

lemma leftReg_mul {d : ℕ} (g g' : FreeGroup (Fin d)) :
    leftReg (g * g') = leftReg g * leftReg g' := by
  ext f h
  simp only [leftReg_apply, mul_apply_eq_comp, mul_inv_rev, mul_assoc]

lemma leftReg_one {d : ℕ} : leftReg (1 : FreeGroup (Fin d)) = 1 := by
  ext f h
  simp [leftReg_apply]

lemma star_leftReg {d : ℕ} (g : FreeGroup (Fin d)) : star (leftReg g) = leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

lemma wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    wordEval (sLimit d) w = leftReg (wordFree w) := by
  induction w with
  | nil => simp [wordEval, wordFree, leftReg_one]
  | cons a w ih =>
    simp only [wordEval, wordFree, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, leftReg_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [leftReg_one]
    · simp [letterOp, sLimit]
    · simp [letterOp, sLimit, star_leftReg]


variable {d : ℕ}

theorem inner_single_left' {n : ℕ} (x : Fin n) (v : L2Free d)
    (z : PiLp 2 (fun _ : Fin n => L2Free d)) :
    ⟪PiLp.single 2 x v, z⟫_ℂ = ⟪v, z x⟫_ℂ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    simp [PiLp.single_apply, hb]
  · simp

theorem leftReg_delta (g : FreeGroup (Fin d)) : leftReg g (delta 1) = delta g := by
  ext h
  simp [delta, leftReg_apply, lp.single_apply, Pi.single_apply, inv_mul_eq_one]
  split_ifs <;> simp_all

theorem wordEval_delta (w : List (Letter d)) :
    wordEval (sLimit d) w (delta 1) = delta (wordFree w) := by
  rw [wordEval_sLimit, leftReg_delta]

theorem inner_delta (u g : FreeGroup (Fin d)) :
    ⟪delta u, delta g⟫_ℂ = if g = u then 1 else 0 := by
  by_cases h : g = u <;> simp [delta, lp.inner_single_left, lp.single_apply, Pi.single_apply, h, eq_comm]

/-- The matrix element of `Xprod`. -/
theorem matrix_element_Xprod (L : Lin d) (m : ℕ) (x y : Fin L.Dm) (u : FreeGroup (Fin d)) :
    ⟪PiLp.single 2 x (delta u), Xprod L m (PiLp.single 2 y (delta 1))⟫_ℂ =
      ∑ i : Fin m → Letter d, Bprod L m i x y * (if wordFree (List.ofFn i) = u then 1 else 0) := by
  rw [Xprod_eq, XprodU_expand]
  rw [sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_single_left', tr_tensorOp_apply, inner_sum, Finset.sum_eq_single y]
  · have hz : (PiLp.single (β := fun _ : Fin L.Dm => L2Free d) 2 y (delta 1)).ofLp y = delta 1 := by simp [PiLp.single_apply]
    rw [hz, wordEval_delta, inner_smul_right, inner_delta]
  · intro b _ hb
    simp [PiLp.single_apply, hb]
  · simp

theorem norm_single_delta (L : Lin d) (x : Fin L.Dm) (u : FreeGroup (Fin d)) :
    ‖PiLp.single (β := fun _ : Fin L.Dm => L2Free d) 2 x (delta u)‖ = 1 := by
  simp [delta]

theorem norm_Xprod_le (L : Lin d) (r : ℝ) (hr : ∀ j, ‖Xop L j‖ ≤ r) :
    ∀ m : ℕ, ‖Xprod L m‖ ≤ r ^ m := by
  intro m
  induction m with
  | zero =>
    have : Xprod L 0 = ContinuousLinearMap.id ℂ _ := by simp [Xprod]; rfl
    rw [this]; simpa using ContinuousLinearMap.norm_id_le
  | succ m ih =>
    have h : Xprod L (m + 1) = Xprod L m * Xop L (m + 1) := XprodU_succ L (sLimit d) m
    rw [h, pow_succ]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h0 : 0 ≤ r := (norm_nonneg _).trans (hr 0)
    exact mul_le_mul ih (hr _) (norm_nonneg _) (pow_nonneg h0 _)

theorem core_bound_one (L : Lin d) (D : ℕ) (hD : 1 ≤ D) (hDm : D ≤ L.Dm) (hS : L.Supp D)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ j, ‖Xop L j‖ ≤ R ^ (1 / (L.q : ℝ))) (p : ℕ) (hp : 1 ≤ p) :
    ‖∑ i : Fin (p * L.q) → Letter d, aCoef L D (p * L.q) i *
        (if wordFree (List.ofFn i) = 1 then (1 : ℂ) else 0)‖ ≤ (L.Dm : ℝ) * R ^ p := by
  set m := p * L.q with hm
  have hq : (1 : ℝ) ≤ L.q := by exact_mod_cast L.hq
  have hnorm : ‖Xprod L m‖ ≤ R ^ p := by
    refine (norm_Xprod_le L _ hR m).trans (le_of_eq ?_)
    have h : (R ^ (1 / (L.q : ℝ))) ^ L.q = R := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hR0, one_div, inv_mul_cancel₀ (by positivity),
        Real.rpow_one]
    rw [hm, mul_comm, pow_mul, h]
  have key : ∑ i : Fin m → Letter d, aCoef L D m i *
        (if wordFree (List.ofFn i) = 1 then (1 : ℂ) else 0) =
      (D : ℂ)⁻¹ * ∑ x : Fin L.Dm, ⟪PiLp.single (β := fun _ : Fin L.Dm => L2Free d) 2 x (delta 1),
        Xprod L m (PiLp.single (β := fun _ : Fin L.Dm => L2Free d) 2 x (delta 1))⟫_ℂ := by
    simp_rw [matrix_element_Xprod, aCoef, Matrix.trace, Matrix.diag, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [key, norm_mul]
  have hDpos : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD1 : ‖(D : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv]; simp
    exact inv_le_one_of_one_le₀ (by simpa using hDpos)
  have hsum : ‖∑ x : Fin L.Dm, ⟪PiLp.single (β := fun _ : Fin L.Dm => L2Free d) 2 x (delta 1),
        Xprod L m (PiLp.single (β := fun _ : Fin L.Dm => L2Free d) 2 x (delta 1))⟫_ℂ‖ ≤
      (L.Dm : ℝ) * R ^ p := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ x : Fin L.Dm, ‖⟪PiLp.single (β := fun _ : Fin L.Dm => L2Free d) 2 x (delta 1),
        Xprod L m (PiLp.single (β := fun _ : Fin L.Dm => L2Free d) 2 x (delta 1))⟫_ℂ‖ ≤
        R ^ p := by
      intro x
      refine (norm_inner_le_norm _ _).trans ?_
      refine (mul_le_mul_of_nonneg_left ((Xprod L m).le_opNorm _) (norm_nonneg _)).trans ?_
      rw [norm_single_delta]
      have := mul_le_mul_of_nonneg_left hnorm (zero_le_one' ℝ)
      simpa using hnorm
    refine (Finset.sum_le_sum fun x _ => this x).trans ?_
    simp
  calc _ ≤ 1 * ((L.Dm : ℝ) * R ^ p) :=
        mul_le_mul hD1 hsum (norm_nonneg _) zero_le_one
    _ = _ := one_mul _


end StrongConv.S9.PartCoreOne

end
end
end

section
section
open Polynomial Filter Topology
noncomputable section
open scoped Classical
namespace StrongConv.S9
open StrongConv
variable {d : ℕ}

theorem core_bound_one (L : Lin d) (D : ℕ) (hD : 1 ≤ D) (hDm : D ≤ L.Dm) (hS : L.Supp D)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ j, ‖Xop L j‖ ≤ R ^ (1 / (L.q : ℝ))) (p : ℕ) (hp : 1 ≤ p) :
    ‖∑ i : Fin (p * L.q) → Letter d, aCoef L D (p * L.q) i *
        (if wordFree (List.ofFn i) = 1 then (1 : ℂ) else 0)‖ ≤ (L.Dm : ℝ) * R ^ p := PartCoreOne.core_bound_one L D hD hDm hS R hR0 hR p hp

end StrongConv.S9

end
end
end

section
section
set_option autoImplicit true
open Polynomial Filter Topology

noncomputable section

open scoped Classical

namespace StrongConv.S9

open StrongConv

/-! ## An analytic lemma: polynomial-times-geometric moment bounds -/

theorem limsup_pow_le (a : ℕ → ℝ) (K0 : ℝ) (s : ℕ) (R : ℝ) (hR : 0 < R) (hK : 0 ≤ K0)
    (h : ∀ p : ℕ, 1 ≤ p → |a p| ≤ K0 * ((p : ℝ) + 1) ^ s * R ^ p) :
    limsup (fun p : ℕ => |a p| ^ (1 / (p : ℝ))) atTop ≤ R := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  -- choose θ > 1 with θ * R ≤ R + δ
  set θ : ℝ := 1 + δ / (2 * R) with hθ
  have hθ1 : 1 < θ := by rw [hθ]; have : 0 < δ / (2 * R) := by positivity
                         linarith
  have hθR : θ * R ≤ R + δ := by
    rw [hθ]; field_simp; linarith
  -- eventually K0 * 2^s * p^s ≤ θ^p
  have ht := tendsto_pow_const_div_const_pow_of_one_lt s hθ1
  have hev : ∀ᶠ p : ℕ in atTop, K0 * 2 ^ s * ((p : ℝ) ^ s / θ ^ p) < 1 := by
    have h2 : Tendsto (fun p : ℕ => K0 * 2 ^ s * ((p : ℝ) ^ s / θ ^ p)) atTop (𝓝 (K0 * 2 ^ s * 0)) :=
      ht.const_mul _
    rw [mul_zero] at h2
    exact h2.eventually (gt_mem_nhds one_pos)
  have hev2 : ∀ᶠ p : ℕ in atTop, |a p| ^ (1 / (p : ℝ)) ≤ θ * R := by
    filter_upwards [hev, eventually_ge_atTop 1] with p hp hp1
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
    have hp1' : (p : ℝ) + 1 ≤ 2 * p := by
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp1
      linarith
    have hb : |a p| ≤ (θ * R) ^ p := by
      refine (h p hp1).trans ?_
      have hq : K0 * ((p : ℝ) + 1) ^ s ≤ θ ^ p := by
        have h1 : K0 * ((p : ℝ) + 1) ^ s ≤ K0 * 2 ^ s * (p : ℝ) ^ s := by
          rw [mul_assoc, ← mul_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp1' s) hK
        have h2 : K0 * 2 ^ s * (p : ℝ) ^ s ≤ θ ^ p := by
          have hθp : (0 : ℝ) < θ ^ p := by positivity
          have e : K0 * 2 ^ s * (p : ℝ) ^ s = (K0 * 2 ^ s * ((p : ℝ) ^ s / θ ^ p)) * θ ^ p := by
            field_simp
          rw [e]
          calc _ ≤ 1 * θ ^ p := mul_le_mul_of_nonneg_right hp.le hθp.le
            _ = θ ^ p := one_mul _
        exact h1.trans h2
      calc K0 * ((p : ℝ) + 1) ^ s * R ^ p ≤ θ ^ p * R ^ p :=
            mul_le_mul_of_nonneg_right hq (by positivity)
        _ = (θ * R) ^ p := (mul_pow _ _ _).symm
    calc |a p| ^ (1 / (p : ℝ)) ≤ ((θ * R) ^ p) ^ (1 / (p : ℝ)) :=
          Real.rpow_le_rpow (abs_nonneg _) hb (by positivity)
      _ = θ * R := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          rw [mul_one_div_cancel hpR.ne', Real.rpow_one]
  have : limsup (fun p : ℕ => |a p| ^ (1 / (p : ℝ))) atTop ≤ θ * R := by
    apply limsup_le_of_le
    · refine isCoboundedUnder_le_of_le atTop (x := 0) fun p => ?_
      exact Real.rpow_nonneg (abs_nonneg _) _
    · exact hev2
  linarith


/-! ## The root exponent -/

theorem rootExp_spec {d : ℕ} (u : FreeGroup (Fin d)) (hu : u ≠ 1) :
    ∃ v : FreeGroup (Fin d), IsNonPower v ∧ 1 ≤ rootExp u ∧ u = v ^ rootExp u := by
  have h := root_exists u hu
  unfold rootExp
  rw [dif_pos h]
  have h2 := Classical.choose_spec h
  have h3 := Classical.choose_spec h2
  exact ⟨_, h3.1, h3.2.1, h3.2.2⟩

theorem rootExp_eq {d : ℕ} (u v : FreeGroup (Fin d)) (k : ℕ) (hv : IsNonPower v) (hk : 1 ≤ k)
    (h : u = v ^ k) : rootExp u = k := by
  have hu : u ≠ 1 := by
    intro h1
    have hv1 : v ≠ 1 := hv.1
    have := root_length v k hv1
    rw [← h, h1] at this
    simp at this
    omega
  obtain ⟨v₀, hv₀, hk₀, h₀⟩ := rootExp_spec u hu
  exact root_unique v₀ v _ k hv₀ hv hk₀ hk (h₀.symm.trans h)


/-! ## The moment bound -/


/-! ## Corollary 9.7 -/


end StrongConv.S9

end
end
end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5

/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-! ## Part Root: roots in free groups -/

/-! ## Part Perm: words as permutations -/

/-! ## Part Comb: the expected number of fixed points -/

/-! ## Part Alg: clearing denominators -/

end StrongConv.S5
end
end

section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartPerm

open scoped InnerProductSpace

/-! ### The left-regular representation -/

end StrongConv.S5.PartPerm
end
end

section
/-!
# Part Comb: the expected number of fixed points of a random word permutation

Proof of `StrongConv.S5.exists_fixCount_expectation` (stated in `Blueprint.lean`).
-/

open Finset

noncomputable section

namespace StrongConv.S5.PartComb

open StrongConv StrongConv.S5

/-! ## Counting permutations extending a partial injection -/

section Count

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A finite set of pairs is the graph of a partial injection. -/
def PInj (E : Finset (α × α)) : Prop :=
  ∀ p ∈ E, ∀ q ∈ E, (p.1 = q.1 ↔ p.2 = q.2)

instance (E : Finset (α × α)) : Decidable (PInj E) := by
  unfold PInj; infer_instance

end Count

/-! ## Paths along a word -/

section Word

variable {d : ℕ} (w : List (Letter d))

/-- The label `i` of a letter `sᵢ` or `sᵢ*`. -/
def lab : Letter d → Option (Fin d)
  | none => none
  | some (Sum.inl i) => some i
  | some (Sum.inr i) => some i

/-- The directed edge `(a', b')` with `σᵢ a' = b'` forced by a step `xₜ = letter (xₜ₊₁)`, where
`a = xₜ`, `b = xₜ₊₁`. -/
def edge {α : Type*} : Letter d → α → α → α × α
  | some (Sum.inl _), a, b => (b, a)
  | _, a, b => (a, b)

/-- The edge set of label `i` of a path. -/
def Es {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) (i : Fin d) :
    Finset (α × α) :=
  (univ.filter fun t : Fin w.length => lab (w.get t) = some i).image
    fun t => edge (w.get t) (x t.castSucc) (x t.succ)

/-- The path stands still at the `none` letters. -/
def Cons {α : Type*} (x : Fin (w.length + 1) → α) : Prop :=
  ∀ t : Fin w.length, w.get t = none → x t.castSucc = x t.succ

/-- A closed consistent path whose edge sets are partial injections. -/
def Good {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) : Prop :=
  Cons w x ∧ (∀ i, PInj (Es w x i)) ∧ x 0 = x (Fin.last _)

instance {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) : Decidable (Cons w x) := by
  unfold Cons; infer_instance

instance {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) :
    Decidable (Good w x) := by
  unfold Good; infer_instance

/-- `σ` realises the path `x`. -/
def Rz {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) : Prop :=
  ∀ t : Fin w.length, x t.castSucc = letterPerm σ (w.get t) (x t.succ)

instance {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Decidable (Rz w σ x) := by
  unfold Rz; infer_instance

end Word

/-! ## Canonical representatives of kernels -/

section Canon

variable {n : ℕ} {α : Type*} [DecidableEq α]

end Canon

/-! ## Invariance under relabelling -/

section Invariance

variable {d : ℕ} (w : List (Letter d))

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

variable (c : Fin (w.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ

end Invariance

/-! ## The bounds on the invariants -/

section Bounds

variable {d : ℕ} (w : List (Letter d)) {α : Type*} [DecidableEq α]

end Bounds

end StrongConv.S5.PartComb
end
end

section
/-!
# CGTvH Lemma 5.2 (Nica): Blueprint

`E[fix w(σ)] = ∑_{c} N^{(V c)} / ∏ᵢ N^{(Eᵢ c)}` over the canonical consistent colourings `c` of the
closed path of `w` (S5 PartComb). For `w` replaced by `r^k`, `r` a cyclically reduced word of a
conjugate of the non-power `v`, every colouring has `V ≤ E`, and exactly `d(k)` have `V = E`
(the periodic ones).
-/

open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb

noncomputable section

namespace StrongConv.N52

/-- The inverse letter. -/
def letterInv {d : ℕ} : Letter d → Letter d
  | none => none
  | some s => some s.swap

/-- `r` is cyclically reduced: no letter is followed (cyclically) by its inverse. -/
def CycRed {d : ℕ} (r : List (Letter d)) : Prop :=
  ∀ t : Fin r.length,
    r.get ⟨(t.val + 1) % r.length, Nat.mod_lt _ (by have := t.2; omega)⟩ ≠ letterInv (r.get t)

/-- `r^k` as a word. -/
def powList {d : ℕ} (r : List (Letter d)) (k : ℕ) : List (Letter d) :=
  (List.replicate k r).flatten

/-! ## Part W: words and free groups -/

/-! ## Part G: the colourings -/

/-! ## Part M: assembly -/

end StrongConv.N52
end
end

section
open Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartG

section Gen

variable {d : ℕ} {α : Type*} [DecidableEq α]

/-- The labelled edge of step `t`. -/
def ee (a : ℕ → Letter d) (x : ℕ → α) (t : ℕ) : Option (Fin d) × (α × α) :=
  (lab (a t), edge (a t) (x t) (x (t + 1)))

/-- The vertices visited at times `≤ k`. -/
def UU (x : ℕ → α) (k : ℕ) : Finset α := (range (k + 1)).image x

/-- The labelled edges of steps `< k`. -/
def EE (a : ℕ → Letter d) (x : ℕ → α) (k : ℕ) : Finset (Option (Fin d) × (α × α)) :=
  (range k).image (ee a x)

/-- Step `k` is a closing step. -/
def closing (a : ℕ → Letter d) (x : ℕ → α) (k : ℕ) : Prop :=
  x (k + 1) ∈ UU x k ∧ ee a x k ∉ EE a x k

instance (a : ℕ → Letter d) (x : ℕ → α) : DecidablePred (closing a x) := by
  intro k; unfold closing; infer_instance

variable {L : ℕ} {a : ℕ → Letter d} {x : ℕ → α}

end Gen

section Bridge

variable {d : ℕ}

/-- The letters of a word, `none` past its end. -/
def A (u : List (Letter d)) (t : ℕ) : Letter d := u.getD t none

end Bridge

section Divisors

variable {d : ℕ}

lemma getD_flat {β : Type*} (s : List β) (dflt : β) (hs : s ≠ []) :
    ∀ j t, t < j * s.length →
      ((List.replicate j s).flatten).getD t dflt = s.getD (t % s.length) dflt
  | 0, t, h => by simp at h
  | j + 1, t, h => by
      rw [List.replicate_succ, List.flatten_cons]
      by_cases ht : t < s.length
      · rw [List.getD_append _ _ _ _ ht, Nat.mod_eq_of_lt ht]
      · rw [Nat.succ_mul] at h
        rw [List.getD_append_right _ _ _ _ (by omega), getD_flat s dflt hs j _ (by omega)]
        congr 1
        conv_rhs => rw [show t = t - s.length + s.length by omega]
        rw [Nat.add_mod_right]

lemma A_pow (r : List (Letter d)) (hne : r ≠ []) (k t : ℕ) (ht : t < k * r.length) :
    A (powList r k) t = A r (t % r.length) :=
  getD_flat r none hne k t ht

lemma wordFree_append (l1 l2 : List (Letter d)) :
    wordFree (l1 ++ l2) = wordFree l1 * wordFree l2 := by
  unfold wordFree; rw [List.map_append, List.prod_append]

lemma wordFree_flat (s : List (Letter d)) : ∀ j,
    wordFree ((List.replicate j s).flatten) = wordFree s ^ j
  | 0 => by simp [wordFree]
  | j + 1 => by
      rw [List.replicate_succ, List.flatten_cons, wordFree_append, wordFree_flat s j, pow_succ']

/-- `p` is a period of `f`. -/
def IsPer {β : Type*} (f : ℕ → β) (p : ℕ) : Prop := ∀ t, f (t + p) = f t

lemma per_mul {β : Type*} {f : ℕ → β} {p : ℕ} (h : IsPer f p) : ∀ m, IsPer f (p * m)
  | 0 => fun t => by simp
  | m + 1 => fun t => by
      rw [Nat.mul_succ, ← add_assoc, h, per_mul h m t]

lemma per_sub {β : Type*} {f : ℕ → β} {p q : ℕ} (hp : IsPer f p) (hq : IsPer f q) (hqp : q ≤ p) :
    IsPer f (p - q) := fun t => by
  rw [← hq (t + (p - q)), add_assoc, Nat.sub_add_cancel hqp, hp]

lemma per_gcd {β : Type*} (f : ℕ → β) (m n : ℕ) : IsPer f m → IsPer f n → IsPer f (Nat.gcd m n) := by
  induction m, n using Nat.gcd.induction with
  | H0 n => intro _ hn; simpa using hn
  | H1 m n hm ih =>
    intro hpm hpn
    rw [Nat.gcd_rec]
    apply ih _ hpm
    have e : n % m = n - m * (n / m) := by
      have := Nat.div_add_mod n m; omega
    rw [e]
    exact per_sub hpn (per_mul hpm _) (Nat.mul_div_le n m)

lemma A_take (r : List (Letter d)) {g j : ℕ} (hj : j < g) : A (r.take g) j = A r j := by
  unfold A
  simp [List.getD_eq_getElem?_getD, hj]

lemma per_dvd (r : List (Letter d)) (hne : r ≠ []) (hnp : IsNonPower (wordFree r)) (k : ℕ)
    (hk : 1 ≤ k) (M : ℕ) (hM : 1 ≤ M) (hML : M ∣ k * r.length)
    (hper : ∀ t < k * r.length, A (powList r k) t = A (powList r k) (t % M)) :
    r.length ∣ M := by
  have hn0 : 0 < r.length := List.length_pos_iff.2 hne
  have hL0 : 0 < k * r.length := Nat.mul_pos (by omega) hn0
  have hnL : r.length ∣ k * r.length := Dvd.intro_left k rfl
  let f : ℕ → Letter d := fun t => A r (t % r.length)
  have hfL : ∀ t, f t = A (powList r k) (t % (k * r.length)) := by
    intro t
    rw [A_pow r hne k _ (Nat.mod_lt _ hL0), Nat.mod_mod_of_dvd _ hnL]
  have hfM : ∀ t, f t = A (powList r k) (t % M) := by
    intro t; rw [hfL, hper _ (Nat.mod_lt _ hL0), Nat.mod_mod_of_dvd _ hML]
  have pn : IsPer f r.length := fun t => by simp only [f, Nat.add_mod_right]
  have pM : IsPer f M := fun t => by rw [hfM, hfM, Nat.add_mod_right]
  have pg := per_gcd f M r.length pM pn
  set g := Nat.gcd M r.length with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgn : g ∣ r.length := Nat.gcd_dvd_right M r.length
  have hgle : g ≤ r.length := Nat.le_of_dvd hn0 hgn
  have hrt : ∀ t < r.length, A r t = A r (t % g) := by
    intro t ht
    have h1 : f t = A r t := by simp only [f, Nat.mod_eq_of_lt ht]
    have h2 : f (t % g) = A r (t % g) := by
      simp only [f, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) ht)]
    rw [← h1, ← h2]
    conv_lhs => rw [← Nat.mod_add_div t g]
    exact per_mul pg (t / g) (t % g)
  have htk : (r.take g).length = g := by simp [hgle]
  have htk0 : r.take g ≠ [] := by
    intro h; rw [h] at htk; simp at htk; omega
  have hreq : r = (List.replicate (r.length / g) (r.take g)).flatten := by
    have hlen : ((List.replicate (r.length / g) (r.take g)).flatten).length = r.length := by
      simp [List.length_flatten, List.map_replicate, List.sum_replicate, htk,
        Nat.div_mul_cancel hgn]
    apply List.ext_getElem hlen.symm
    intro t h1 h2
    rw [← List.getD_eq_getElem _ none h1, ← List.getD_eq_getElem _ none h2,
      getD_flat _ none htk0 _ t (by rw [htk, Nat.div_mul_cancel hgn]; exact h1), htk]
    show A r t = A (r.take g) (t % g)
    rw [A_take r (Nat.mod_lt _ hg0)]
    exact hrt t h1
  have hw : wordFree r = wordFree (r.take g) ^ (r.length / g) := by
    conv_lhs => rw [hreq]
    exact wordFree_flat _ _
  have h1 : r.length / g < 2 := by
    by_contra h
    exact hnp.2 _ _ (by omega) hw
  have h2 : 0 < r.length / g := Nat.div_pos hgle hg0
  have h3 : r.length = g := by
    have := Nat.div_mul_cancel hgn
    rw [show r.length / g = 1 by omega, one_mul] at this
    exact this.symm
  rw [h3]
  exact Nat.gcd_dvd_left M r.length

end Divisors

end StrongConv.N52.PartG
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartM

/-- `N^{(m)} / N^m → 1`. -/
lemma tendsto_descFactorial_div_pow (m : ℕ) :
    Tendsto (fun N : ℕ => (N.descFactorial m : ℝ) / (N : ℝ) ^ m) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => ∏ j ∈ range m, (1 - (j : ℝ) / N)) atTop
      (𝓝 (∏ j ∈ range m, (1 - 0 : ℝ))) :=
    tendsto_finsetProd _ fun j _ =>
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ))
  simp only [sub_zero, prod_const_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (max m 1)] with N hN
  have hNm : m ≤ N := le_of_max_le_left hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : 1 ≤ N := le_of_max_le_right hN
    exact_mod_cast (show N ≠ 0 by omega)
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod,
    show (N : ℝ) ^ m = ∏ _j ∈ range m, (N : ℝ) by simp, ← prod_div_distrib]
  refine prod_congr rfl fun j hj => ?_
  have hj : j < m := mem_range.1 hj
  rw [Nat.cast_sub (by omega), sub_div, div_self hN0]

/-- `N^a / N^b → [a = b]` for `a ≤ b`. -/
lemma tendsto_pow_div_pow (a b : ℕ) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ a / (N : ℝ) ^ b) atTop (𝓝 (if a = b then 1 else 0)) := by
  split_ifs with h
  · subst h
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [div_self (pow_ne_zero _ hN0)]
  · have h1 : Tendsto (fun N : ℕ => ((N : ℝ) ^ (b - a))⁻¹) atTop (𝓝 0) :=
      ((tendsto_pow_atTop (by omega : b - a ≠ 0)).comp
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [pow_sub₀ _ hN0 hab]
    field_simp

lemma tendsto_term {ι : Type*} [Fintype ι] (a : ℕ) (b : ι → ℕ) (hab : a ≤ ∑ i, b i) :
    Tendsto (fun N : ℕ => (N.descFactorial a : ℝ) / ∏ i, (N.descFactorial (b i) : ℝ)) atTop
      (𝓝 (if a = ∑ i, b i then 1 else 0)) := by
  have hA := tendsto_descFactorial_div_pow a
  have hB : Tendsto (fun N : ℕ => ∏ i, (N.descFactorial (b i) : ℝ) / (N : ℝ) ^ (b i)) atTop
      (𝓝 (∏ _i : ι, (1 : ℝ))) :=
    tendsto_finsetProd _ fun i _ => tendsto_descFactorial_div_pow (b i)
  rw [prod_const_one] at hB
  have hP := tendsto_pow_div_pow a (∑ i, b i) hab
  have h := (hA.div hB one_ne_zero).mul hP
  rw [div_one, one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp only [Pi.div_apply]
  rw [prod_div_distrib, prod_pow_eq_pow_sum]
  by_cases hz : ∏ i, (N.descFactorial (b i) : ℝ) = 0
  · simp [hz]
  · field_simp

end StrongConv.N52.PartM
end
end

section
open Filter Topology Finset
open StrongConv StrongConv.S5 StrongConv.S5.PartComb StrongConv.N52
noncomputable section
namespace StrongConv.N52.PartW

/-! ## Cyclically reduced representatives -/

/-- A letter of a reduced word of `FreeGroup (Fin d)` as a `Letter d`. -/
def toLetter {d : ℕ} (p : Fin d × Bool) : Letter d :=
  if p.2 then some (Sum.inl p.1) else some (Sum.inr p.1)

lemma toLetter_ne_none {d : ℕ} (p : Fin d × Bool) : toLetter p ≠ none := by
  unfold toLetter; split <;> simp

lemma toLetter_injective {d : ℕ} : Function.Injective (toLetter (d := d)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  cases a <;> cases b <;> simp_all [toLetter]

lemma letterInv_toLetter {d : ℕ} (p : Fin d × Bool) :
    letterInv (toLetter p) = toLetter (p.1, !p.2) := by
  rcases p with ⟨i, a⟩
  cases a <;> rfl

lemma wordFree_cons {d : ℕ} (l : Letter d) (w : List (Letter d)) :
    wordFree (l :: w) = wordFree [l] * wordFree w := by
  simp [wordFree]

lemma wordFree_map_toLetter {d : ℕ} (R : List (Fin d × Bool)) :
    wordFree (R.map toLetter) = FreeGroup.mk R := by
  induction R with
  | nil => simp [wordFree, FreeGroup.one_eq_mk]
  | cons a R ih =>
    rw [List.map_cons, wordFree_cons, ih,
      show a :: R = [a] ++ R from rfl, ← FreeGroup.mul_mk]
    congr 1
    rcases a with ⟨i, b⟩
    cases b
    · simp [wordFree, toLetter, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
    · simp [wordFree, toLetter, FreeGroup.of]

theorem exists_cyc_rep {d : ℕ} (v : FreeGroup (Fin d)) (hv : IsNonPower v) :
    ∃ (r : List (Letter d)) (h : FreeGroup (Fin d)), r ≠ [] ∧ (∀ l ∈ r, l ≠ none) ∧
      CycRed r ∧ wordFree r = h * v * h⁻¹ := by
  classical
  set L := v.toWord
  set R := FreeGroup.reduceCyclically L with hRdef
  set C := FreeGroup.reduceCyclically.conjugator L
  have hconj := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically L
  have hv' : v = FreeGroup.mk C * FreeGroup.mk R * (FreeGroup.mk C)⁻¹ := by
    rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk, hconj, FreeGroup.mk_toWord]
  have hRc : FreeGroup.IsCyclicallyReduced R :=
    FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord
  refine ⟨R.map toLetter, (FreeGroup.mk C)⁻¹, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [List.map_eq_nil_iff] at h0
    apply hv.1
    rw [hv', h0, ← FreeGroup.one_eq_mk]
    group
  · intro l hl
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hl
    exact toLetter_ne_none p
  · intro t
    simp only [List.get_eq_getElem, List.getElem_map, letterInv_toLetter]
    intro heq
    have heq := toLetter_injective heq
    have ht := t.2
    simp only [List.length_map] at ht
    by_cases h1 : t.val + 1 < R.length
    · have hm : (t.val + 1) % (R.map toLetter).length = t.val + 1 := by
        simp only [List.length_map]; exact Nat.mod_eq_of_lt h1
      simp only [hm] at heq
      have := hRc.isReduced.getElem t.val h1
      rw [heq] at this
      simp at this
    · have hn : t.val + 1 = R.length := by omega
      have hm : (t.val + 1) % (R.map toLetter).length = 0 := by
        simp only [List.length_map, hn, Nat.mod_self]
      simp only [hm] at heq
      have hlast : R.getLast? = some R[t.val] := by
        rw [List.getLast?_eq_getElem?]
        have e : R.length - 1 = t.val := by omega
        simp only [e]
        exact List.getElem?_eq_getElem _
      have hhead : R.head? = some R[0] := by
        rw [List.head?_eq_getElem?]; simp
      have := hRc.2 R[t.val] (by rw [hlast]; rfl) R[0] (by rw [hhead]; rfl)
      rw [heq] at this
      simp at this
  · rw [wordFree_map_toLetter, hv']
    group

/-! ## Powers and conjugation -/

/-! ## Properties of `r ^ k` -/

/-! ## The expectation formula -/

end StrongConv.N52.PartW
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L2
open StrongConv
/-!
# q202: Blueprint for the stable Lemma 10.4 analogue (`supp_subset_Icc_of_stableExpTr_expansion`)

CGTvH p. 32. `Solutions.StrongConvStable.Q202S9` is the proof of Corollary 9.7 (namespace
`StrongConv.S9`: the padded linearization `Lin`, `aCoef`, `core_bound_one`, `limsup_pow_le`) with a
weighted `core_bound_w` added.

* `stable_linearization`: Lemma 9.1 for `E[Tr P(Πᴺ)^p]` (the stable copy of `linearization_data`).
* `chiE_trivial`, `avg_trace_zero`: `Tr π_N(1) = D_N`; `∑_τ Tr π_N(τ) = 0` without a trivial summand.
* `multiwalk_limit` (S5): the joint fixed-point moments of powers of a cyclically reduced non-power
  converge to a limit `F s m` that does not depend on the word (Hanany–Puder [32], Nica).
* `stable_limit` (Lemma 10.2): `E[Tr π_N(w(σ))] → ϖ`, `|ϖ| ≤ c k^β`, `ϖ = 0` for `k = 1`.
* `stable_moment_bound`: `|ν_i(x^p)| ≤ K₀ (p+1)^s (‖P(s)‖ + ε)^p` (Lemmas 9.2, 9.6 as on p. 32).
-/
/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-- The permutation a word stands for (product in the order the letters appear). -/
def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

/-- Number of fixed points. -/
def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => π x = x).card

/-- The inverse letter. -/
def letterInv {d : ℕ} : Letter d → Letter d
  | none => none
  | some s => some s.swap

/-- `r` is cyclically reduced: no letter is followed (cyclically) by its inverse. -/
def CycRed {d : ℕ} (r : List (Letter d)) : Prop :=
  ∀ t : Fin r.length,
    r.get ⟨(t.val + 1) % r.length, Nat.mod_lt _ (by have := t.2; omega)⟩ ≠ letterInv (r.get t)

/-- `r^k` as a word. -/
def powList {d : ℕ} (r : List (Letter d)) (k : ℕ) : List (Letter d) :=
  (List.replicate k r).flatten

/-- `E[Tr h(P(Πᴺ, Πᴺ*))] / N^α`, the left side of the stable Lemma 10.3 / 10.4. -/
def stE (π : StableRep) {D d : ℕ} (P : NCPoly D d) (N : ℕ) (h : ℝ → ℝ) : ℝ :=
  uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
    (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
      ((fnCalc h (P.eval (π.model σ)) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
      (N : ℝ) ^ π.alpha)

/-- `E[Tr π_N(w(σ))]`. -/
def chiE (π : StableRep) {d : ℕ} (N : ℕ) (w : List (Letter d)) : ℂ :=
  (∑ σ : Fin d → Equiv.Perm (Fin N),
      (π.π N (wordPerm σ w) : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace) /
    (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℂ)

end StrongConv.Q202L2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L2.PartX
open StrongConv StrongConv.Q202L2
/-!
# q202 leaf 2, Parts Lin and X: `stable_linearization`, `chiE_trivial`, `avg_trace_zero`,
# `stable_limit`, `stable_moment_bound`

`multiwalk_limit` is the Blueprint stub, proved in Part M.
-/
/-! ## Words and permutations -/
theorem wordPerm_eq_lift {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordPerm σ w = FreeGroup.lift σ (wordFree w) := by
  induction w with
  | nil => simp [wordPerm, wordFree]
  | cons a w ih =>
    simp only [wordPerm, wordFree, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    rcases a with _ | (i | i) <;> simp [letterPerm]

lemma wordFree_append {d : ℕ} (w w' : List (Letter d)) :
    wordFree (w ++ w') = wordFree w * wordFree w' := by
  simp [wordFree, List.map_append, List.prod_append]

lemma wordFree_powList {d : ℕ} (r : List (Letter d)) (n : ℕ) :
    wordFree (powList r n) = wordFree r ^ n := by
  induction n with
  | zero => simp [powList, wordFree]
  | succ n ih =>
    rw [powList, List.replicate_succ, List.flatten_cons, wordFree_append, ← powList, ih, pow_succ']

lemma fixCount_conj {N : ℕ} (g h : Equiv.Perm (Fin N)) : fixCount (h * g * h⁻¹) = fixCount g := by
  unfold fixCount
  refine Finset.card_bij (fun x _ => h⁻¹ x) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h2 := hx.2
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h2
    apply h.injective
    rw [h2]; simp
  · intro x _ y _ hxy
    exact h⁻¹.injective hxy
  · intro y hy
    rw [Finset.mem_filter] at hy
    refine ⟨h y, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [Equiv.Perm.mul_apply, hy.2]

lemma xi_eq_fixCount {N : ℕ} (j : ℕ) (g : Equiv.Perm (Fin N)) : xi j g = fixCount (g ^ j) := rfl

lemma fix_conj' {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w r : List (Letter d))
    (v h : FreeGroup (Fin d)) (k : ℕ) (hw : wordFree w = v ^ k)
    (hr : wordFree r = h * v * h⁻¹) (j : ℕ) :
    xi j (wordPerm σ w) = fixCount (wordPerm σ (powList r (k * j))) := by
  rw [xi_eq_fixCount, wordPerm_eq_lift, wordPerm_eq_lift, wordFree_powList, hr, hw, conj_pow,
    map_mul, map_mul, map_inv, ← map_pow, ← pow_mul, fixCount_conj]

/-! ## The model -/
lemma wordEval_model (π : StableRep) {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N))
    (w : List (Letter d)) :
    wordEval (π.model σ) w = Matrix.toEuclideanCLM (𝕜 := ℂ)
      (π.π N (FreeGroup.lift σ (wordFree w)) : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) := by
  induction w with
  | nil => simp [wordEval, wordFree]
  | cons l w ih =>
    simp only [wordEval, wordFree, List.map_cons, List.prod_cons, map_mul,
      Submonoid.coe_mul] at ih ⊢
    rw [ih]
    congr 1
    rcases l with _ | (i | i)
    · simp
    · simp [letterOp, StableRep.model]
    · simp only [letterOp, StableRep.model, ← map_star]
      congr 1
      simp

lemma trace_toEuclideanCLM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ _ ((Matrix.toEuclideanCLM (𝕜 := ℂ) M :
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = M.trace := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.trace_toLin_eq]

lemma trace_wordEval_model (π : StableRep) {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N))
    (w : List (Letter d)) :
    LinearMap.trace ℂ _ ((wordEval (π.model σ) w :
      EuclideanSpace ℂ (Fin (π.dim N)) →L[ℂ] EuclideanSpace ℂ (Fin (π.dim N))) :
        EuclideanSpace ℂ (Fin (π.dim N)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (π.dim N))) =
      (π.π N (wordPerm σ w) : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace := by
  rw [wordEval_model, trace_toEuclideanCLM, wordPerm_eq_lift]

/-! ## Part Lin -/
/-- `g ↦ π_N(σ(g))` as an operator. -/
def piOp (π : StableRep) {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (h : FreeGroup (Fin d)) :
    EuclideanSpace ℂ (Fin (π.dim N)) →L[ℂ] EuclideanSpace ℂ (Fin (π.dim N)) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ)
    (π.π N (FreeGroup.lift σ h) : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ)

lemma final_alg {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (t : κ → ι → ℂ) (M : ℝ)
    (n : ℕ) :
    (∑ k, (∑ i, b i * t k i).re / M) / (n : ℝ) =
      (∑ i, b i * ((∑ k, t k i) / (n : ℂ))).re / M := by
  have : ∑ i, b i * ((∑ k, t k i) / (n : ℂ)) = (∑ k, ∑ i, b i * t k i) / ((n : ℝ) : ℂ) := by
    simp_rw [mul_div_assoc', Finset.mul_sum]
    rw [← Finset.sum_div, Finset.sum_comm]
    push_cast; rfl
  rw [this, Complex.div_ofReal_re, Complex.re_sum, Finset.sum_div, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_right_comm]

theorem transfer_model (π : StableRep) {D d : ℕ} (P : NCPoly D d) (L : S9.Lin d)
    (hlim : P.eval (sLimit d) = S9.PartLin.Tcomp L D (sLimit d)) {N : ℕ}
    (σ : Fin d → Equiv.Perm (Fin N)) :
    P.eval (π.model σ) = S9.PartLin.Tcomp L D (π.model σ) := by
  have h1 := S9.PartLin.eval_expand_fiber P L (sLimit d) leftReg
    (fun w => S9.PartLin.wordEval_sLimit w)
  have h2 := S9.PartLin.Tcomp_expand_fiber P L (sLimit d) leftReg
    (fun w => S9.PartLin.wordEval_sLimit w)
  have h0 : ∑ h ∈ S9.PartLin.tIdx P L,
      tensorOp (S9.PartLin.CP P h - S9.PartLin.CB L h) (leftReg h) = 0 := by
    simp_rw [S9.PartLin.tensorOp_sub_left]
    rw [Finset.sum_sub_distrib, ← h1, ← h2, hlim, sub_self]
  have hc := S9.PartLin.extract (S9.PartLin.tIdx P L)
    (fun h => S9.PartLin.CP P h - S9.PartLin.CB L h) h0
  have hPi : ∀ w, wordEval (π.model σ) w = piOp π σ (wordFree w) :=
    fun w => wordEval_model π σ w
  rw [S9.PartLin.eval_expand_fiber P L (π.model σ) _ hPi,
    S9.PartLin.Tcomp_expand_fiber P L (π.model σ) _ hPi]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [sub_eq_zero.mp (hc h hh)]

theorem stable_linearization (π : StableRep) {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (hD : 1 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : S9.Lin d, D ≤ L.Dm ∧ L.Supp D ∧
      (∀ j, ‖S9.Xop L j‖ ≤ (‖P.eval (sLimit d)‖ + ε) ^ (1 / (L.q : ℝ))) ∧
      ∀ p N : ℕ, 1 ≤ p → 1 ≤ N →
        stE π P N (fun x => x ^ p) =
          (∑ i : Fin (p * L.q) → Letter d,
            (D : ℂ) * S9.aCoef L D (p * L.q) i * chiE π N (List.ofFn i)).re / (N : ℝ) ^ π.alpha := by
  obtain ⟨q, Dim, A, h1, hq', hq1, heq, hnorm⟩ := StrongConv.exists_linearization P ε hε
  have hDm : D ≤ S9.PartLin.DmOf q Dim := h1 ▸ S9.PartLin.Dim_le_DmOf q Dim 1 (by omega)
  have hS1 := S9.PartLin.mkLin_supp1 q hq1 Dim A D h1
  have hlim := S9.PartLin.hlim_of q hq1 Dim A P h1 hq' heq
  refine ⟨S9.PartLin.mkLin q hq1 Dim A, hDm, ⟨hS1, S9.PartLin.mkLin_supp2 q hq1 Dim A D hq'⟩,
    fun j => S9.PartLin.Xop_norm_le q hq1 Dim A _ hnorm j, ?_⟩
  intro p N hp hN
  set L := S9.PartLin.mkLin q hq1 Dim A with hL
  have hT : ∀ σ : Fin d → Equiv.Perm (Fin N),
      LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
        ((fnCalc (fun x => x ^ p) (P.eval (π.model σ)) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) =
      ∑ i : Fin (p * L.q) → Letter d, (S9.Bprod L (p * L.q) i).trace *
        (π.π N (wordPerm σ (List.ofFn i)) : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace := by
    intro σ
    rw [S9.PartLin.fnCalc_pow _ (S9.eval_isSelfAdjoint P hP _), transfer_model π P L hlim σ,
      S9.PartLin.trace_Tcomp_pow L D hDm hS1 (π.model σ) hq1 p hp, S9.PartLin.trace_XprodU]
    simp only [trace_wordEval_model]
  have hD0 : (D : ℂ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hcoef : ∀ i : Fin (p * L.q) → Letter d,
      (D : ℂ) * S9.aCoef L D (p * L.q) i = (S9.Bprod L (p * L.q) i).trace := by
    intro i
    unfold S9.aCoef
    field_simp
  unfold stE uniformExp chiE
  simp_rw [hT, hcoef]
  exact final_alg _ (fun σ i => (π.π N (wordPerm σ (List.ofFn i)) :
    Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace) _ _

end StrongConv.Q202L2.PartX
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L2
open StrongConv
/-! ## Part Lin: the linearization for the stable model -/

end StrongConv.Q202L2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L2.PartX
open StrongConv StrongConv.Q202L2
/-! ## Part X: characters -/
theorem chiE_trivial (π : StableRep) {d : ℕ} (N : ℕ) (w : List (Letter d)) (hw : wordFree w = 1) :
    chiE π N w = (π.dim N : ℂ) := by
  unfold chiE
  have : ∀ σ : Fin d → Equiv.Perm (Fin N), wordPerm σ w = 1 := by
    intro σ; rw [wordPerm_eq_lift, hw, map_one]
  simp only [this, map_one, OneMemClass.coe_one, Matrix.trace_one, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end StrongConv.Q202L2.PartX
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L2
open StrongConv
/-! ## Part X: characters -/

end StrongConv.Q202L2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L2.PartX
open StrongConv StrongConv.Q202L2
theorem avg_trace_zero (π : StableRep) (hπ : π.NoTrivialSummand) (N : ℕ) (hN : π.N₀ ≤ N) :
    ∑ τ : Equiv.Perm (Fin N), (π.π N τ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace = 0 := by
  set Q : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ :=
    ∑ τ : Equiv.Perm (Fin N), (π.π N τ : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) with hQ
  have hinv : ∀ g, (π.π N g : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) * Q = Q := by
    intro g
    rw [hQ, Finset.mul_sum]
    simp_rw [← Submonoid.coe_mul, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun τ => rfl)
  have hQ0 : Q = 0 := by
    ext i j
    have := hπ N hN (fun a => Q a j) (fun g => by
      funext a
      have h := congrArg (fun M => M a j) (hinv g)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h)
    exact congrFun this i
  rw [← Matrix.trace_sum, ← hQ, hQ0, Matrix.trace_zero]

end StrongConv.Q202L2.PartX
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L2
open StrongConv

end StrongConv.Q202L2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {α : Type*} [Fintype α] [DecidableEq α]
/-!
# q202 leaf 2, Part M: `multiwalk_limit` (the several-cycle Nica limit)

The colouring machinery (`PInj`, `Es`, `EsM`, `GoodM`, `canon`, `nv`, …) is copied from
`Q202L1PartR.lean` (sections Count–Multi), whose module does not currently build.

Proof: `E[∏ fix] = ∑_c N^{(v_c)} / ∏_i N^{(e_{c,i})}` over canonical good colourings (`expect_eq`).
Counting used half-edges (`Hs`, `deg`): every vertex of a cyclically reduced closed walk has
degree `≥ 2`, and the half-edges number `2e`, so `v ≤ e` (`nv_le_e`); `v = e` forces degree `2`
everywhere (`deg_le_two`), hence walks through a common vertex run in lockstep forwards or
backwards (`fwd`, `bwd`), so a vertex determines the phase mod `|r|` (`phase`: `r` primitive,
`r` not a rotation of its inverse). Restriction to positions `≡ 0 mod |r|` and periodic extension
are inverse bijections between the `v = e` colourings for `r` and all good colourings of the
walks `g₁^{m_t}` (`card_B`); the latter number `F s m` is `E[∏ fix(σ^{m_t})]` for `N ≥ ∑ m`
(`Fm_bound`), so `F s m ≤ (1 + ∑ m)^s`.
-/
/-- A finite set of pairs is the graph of a partial injection. -/
def PInj (E : Finset (α × α)) : Prop :=
  ∀ p ∈ E, ∀ q ∈ E, (p.1 = q.1 ↔ p.2 = q.2)

instance (E : Finset (α × α)) : Decidable (PInj E) := by
  unfold PInj; infer_instance

lemma card_stab (A : Finset α) :
    (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      (Fintype.card α - A.card).factorial := by
  have e := Equiv.Perm.subtypeEquivSubtypePerm (fun a : α => a ∉ A)
  have h1 : (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      Fintype.card { f : Equiv.Perm α // ∀ a, ¬ (a ∉ A) → f a = a } := by
    rw [Fintype.card_subtype]; congr 1; ext π; simp
  rw [h1, ← Fintype.card_congr e, Fintype.card_perm, Fintype.card_subtype]
  congr 1
  rw [← Finset.card_compl]
  congr 1
  ext a; simp

lemma exists_ext (E : Finset (α × α)) (h : PInj E) :
    ∃ τ : Equiv.Perm α, ∀ p ∈ E, τ p.1 = p.2 := by
  have key : ∀ a ∈ E.image Prod.fst, ∃ p ∈ E, p.1 = a := by
    intro a ha; simpa using ha
  let f : {a // a ∈ E.image Prod.fst} → {b // b ∈ E.image Prod.snd} := fun a =>
    ⟨(Classical.choose (key a.1 a.2)).2,
      mem_image_of_mem _ (Classical.choose_spec (key a.1 a.2)).1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have h1 := Classical.choose_spec (key a.1 a.2)
      have h2 := Classical.choose_spec (key a'.1 a'.2)
      have : (Classical.choose (key a.1 a.2)).2 = (Classical.choose (key a'.1 a'.2)).2 :=
        congrArg Subtype.val haa
      apply Subtype.ext
      rw [← h1.2, ← h2.2]
      exact (h _ h1.1 _ h2.1).2 this
    · intro b
      obtain ⟨q, hq, hqb⟩ := mem_image.1 b.2
      refine ⟨⟨q.1, mem_image_of_mem _ hq⟩, Subtype.ext ?_⟩
      have h1 := Classical.choose_spec (key q.1 (mem_image_of_mem _ hq))
      show (Classical.choose (key q.1 (mem_image_of_mem _ hq))).2 = b.1
      rw [← hqb]
      exact (h _ h1.1 _ hq).1 h1.2
  refine ⟨(Equiv.ofBijective f hf).extendSubtype, fun p hp => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem _ _ (mem_image_of_mem _ hp)]
  have h1 := Classical.choose_spec (key p.1 (mem_image_of_mem _ hp))
  exact (h _ h1.1 _ hp).1 h1.2

lemma card_ext (E : Finset (α × α)) :
    (univ.filter fun τ : Equiv.Perm α => ∀ p ∈ E, τ p.1 = p.2).card =
      if PInj E then (Fintype.card α - E.card).factorial else 0 := by
  split_ifs with h
  · obtain ⟨τ₀, hτ₀⟩ := exists_ext E h
    have hA : (E.image Prod.fst).card = E.card :=
      card_image_of_injOn (fun p hp q hq hpq => Prod.ext hpq ((h p hp q hq).1 hpq))
    rw [← hA, ← card_stab]
    refine card_nbij' (fun τ => τ₀⁻¹ * τ) (fun π => τ₀ * π) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
      intro a ha
      obtain ⟨p, hp, rfl⟩ : ∃ p ∈ E, p.1 = a := by simpa using ha
      rw [Equiv.Perm.mul_apply, hτ p hp, ← hτ₀ p hp]
      simp
    · intro π hπ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
      intro p hp
      rw [Equiv.Perm.mul_apply, hπ p.1 (mem_image_of_mem _ hp), hτ₀ p hp]
    · intro τ _; simp
    · intro π _; simp
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro τ _ hτ
    apply h
    intro p hp q hq
    constructor
    · intro e; rw [← hτ p hp, ← hτ q hq, e]
    · intro e; apply τ.injective; rw [hτ p hp, hτ q hq, e]

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} (w : List (Letter d))
/-! ## Paths along a word -/
/-- The label `i` of a letter `sᵢ` or `sᵢ*`. -/
def lab : Letter d → Option (Fin d)
  | none => none
  | some (Sum.inl i) => some i
  | some (Sum.inr i) => some i

/-- The directed edge `(a', b')` with `σᵢ a' = b'` forced by a step `xₜ = letter (xₜ₊₁)`, where
`a = xₜ`, `b = xₜ₊₁`. -/
def edge {α : Type*} : Letter d → α → α → α × α
  | some (Sum.inl _), a, b => (b, a)
  | _, a, b => (a, b)

lemma edge_cases {α : Type*} (l : Letter d) (a b : α) :
    ((edge l a b).1 = a ∧ (edge l a b).2 = b) ∨ ((edge l a b).1 = b ∧ (edge l a b).2 = a) := by
  rcases l with _ | i | i <;> simp [edge]

lemma edge_map {α β : Type*} (φ : β → α) (l : Letter d) (a b : β) :
    edge l (φ a) (φ b) = Prod.map φ φ (edge l a b) := by
  rcases l with _ | i | i <;> simp [edge]

/-- The edge set of label `i` of a path. -/
def Es {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) (i : Fin d) :
    Finset (α × α) :=
  (univ.filter fun t : Fin w.length => lab (w.get t) = some i).image
    fun t => edge (w.get t) (x t.castSucc) (x t.succ)

/-- The path stands still at the `none` letters. -/
def Cons {α : Type*} (x : Fin (w.length + 1) → α) : Prop :=
  ∀ t : Fin w.length, w.get t = none → x t.castSucc = x t.succ

/-- A closed consistent path whose edge sets are partial injections. -/
def Good {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) : Prop :=
  Cons w x ∧ (∀ i, PInj (Es w x i)) ∧ x 0 = x (Fin.last _)

instance {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) : Decidable (Cons w x) := by
  unfold Cons; infer_instance

instance {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) :
    Decidable (Good w x) := by
  unfold Good; infer_instance

/-- `σ` realises the path `x`. -/
def Rz {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) : Prop :=
  ∀ t : Fin w.length, x t.castSucc = letterPerm σ (w.get t) (x t.succ)

instance {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Decidable (Rz w σ x) := by
  unfold Rz; infer_instance

/-- The path of `y` under `σ`. -/
def path {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) : Fin (w.length + 1) → Fin N :=
  fun t => wordPerm σ (w.drop t) y

lemma wordPerm_cons_apply {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (l : Letter d)
    (ws : List (Letter d)) (y : Fin N) :
    wordPerm σ (l :: ws) y = letterPerm σ l (wordPerm σ ws y) := by
  simp [wordPerm, Equiv.Perm.mul_apply]

lemma path_last {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) :
    path w σ y (Fin.last _) = y := by
  simp [path, wordPerm]

lemma path_zero {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) :
    path w σ y 0 = wordPerm σ w y := by
  simp [path]

lemma path_step {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) (t : Fin w.length) :
    path w σ y t.castSucc = letterPerm σ (w.get t) (path w σ y t.succ) := by
  simp only [path, Fin.val_castSucc, Fin.val_succ]
  rw [List.drop_eq_getElem_cons t.2, wordPerm_cons_apply]
  rfl

lemma eq_path {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N)
    (hx : Rz w σ x) : x = path w σ (x (Fin.last _)) := by
  funext t
  induction t using Fin.reverseInduction with
  | last => rw [path_last]
  | cast t ih => rw [hx t, path_step, ← ih]

lemma fixCount_eq {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    fixCount (wordPerm σ w) =
      (univ.filter fun x : Fin (w.length + 1) → Fin N => Rz w σ x ∧ x 0 = x (Fin.last _)).card := by
  unfold fixCount
  symm
  refine card_nbij' (fun x => x (Fin.last _)) (path w σ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have := eq_path w σ x hx.1
    conv_rhs => rw [← hx.2, this]
    rw [path_zero]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    exact ⟨fun t => path_step w σ y t, by rw [path_zero, path_last, hy]⟩
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    exact (eq_path w σ x hx.1).symm
  · intro y _
    exact path_last w σ y

lemma Rz_iff {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Rz w σ x ↔ Cons w x ∧ ∀ i, ∀ p ∈ Es w x i, σ i p.1 = p.2 := by
  constructor
  · intro h
    refine ⟨fun t ht => by have := h t; rw [ht] at this; simpa [letterPerm] using this, ?_⟩
    intro i p hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
    rw [mem_filter] at ht
    have h' := h t
    generalize w.get t = l at ht h'
    rcases l with _ | j | j
    · simp [lab] at ht
    · simp only [lab, Option.some.injEq] at ht
      obtain ⟨-, rfl⟩ := ht
      simp only [edge]; exact h'.symm
    · simp only [lab, Option.some.injEq] at ht
      obtain ⟨-, rfl⟩ := ht
      simp only [edge, letterPerm] at h' ⊢
      rw [h']; simp
  · rintro ⟨hc, he⟩ t
    have hmem : ∀ j, lab (w.get t) = some j →
        edge (w.get t) (x t.castSucc) (x t.succ) ∈ Es w x j := fun j hj =>
      mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hj⟩, rfl⟩
    have hct := hc t
    generalize w.get t = l at hmem hct
    rcases l with _ | j | j
    · simp [letterPerm, hct rfl]
    · have := he j _ (hmem j rfl)
      simp only [edge] at this
      simp [letterPerm, this]
    · have := he j _ (hmem j rfl)
      simp only [edge] at this
      simp [letterPerm, ← this]

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {n : ℕ} {α : Type*} [DecidableEq α]
/-! ## Canonical representatives of kernels -/
/-- The first position where `x` takes the value `x t`. -/
def canon (x : Fin n → α) (t : Fin n) : Fin n :=
  (univ.filter fun s => x s = x t).min' ⟨t, by simp⟩

lemma canon_spec (x : Fin n → α) (t : Fin n) : x (canon x t) = x t := by
  unfold canon
  exact (mem_filter.1 (min'_mem (univ.filter fun s => x s = x t) _)).2

lemma canon_eq_of_ker {β : Type*} [DecidableEq β] (x : Fin n → α) (y : Fin n → β)
    (h : ∀ s t, x s = x t ↔ y s = y t) : canon x = canon y := by
  funext t
  simp only [canon, h]

lemma canon_ker (x : Fin n → α) (s t : Fin n) : canon x s = canon x t ↔ x s = x t := by
  constructor
  · intro h
    have := congrArg x h
    rwa [canon_spec x s, canon_spec x t] at this
  · intro h
    have : ∀ r, (x r = x s) ↔ (x r = x t) := fun r => by rw [h]
    simp only [canon, this]

lemma canon_canon (x : Fin n → α) : canon (canon x) = canon x :=
  canon_eq_of_ker _ _ (canon_ker x)

lemma canon_canon_apply (x : Fin n → α) (t : Fin n) : canon x (canon x t) = canon x t :=
  (canon_ker x _ _).2 (canon_spec x t)

lemma injOn_canon (x : Fin n → α) : Set.InjOn x (Set.range (canon x)) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
  rw [canon_spec x s, canon_spec x t] at h
  exact (canon_ker x s t).2 h

lemma comp_canon (x : Fin n → α) : x ∘ canon x = x := funext (canon_spec x)

/-- The number of values of a path. -/
def nv (x : Fin n → α) : ℕ := (univ.image x).card

lemma card_fiber [Fintype α] (c : Fin n → Fin n) (hc : canon c = c) :
    (univ.filter fun x : Fin n → α => canon x = c).card =
      (Fintype.card α).descFactorial (nv c) := by
  have hcc : ∀ t, c (c t) = c t := fun t => by
    have := canon_canon_apply c t; rwa [hc] at this
  have hmem : ∀ t, c t ∈ univ.image c := fun t => mem_image_of_mem _ (mem_univ _)
  rw [nv, ← Fintype.card_coe (univ.image c), ← Fintype.card_embedding_eq, ← card_univ]
  refine card_bij' (fun x hx => ⟨fun s => x s.1, ?_⟩) (fun φ _ => fun t => φ ⟨c t, hmem t⟩)
    (fun _ _ => mem_univ _) ?_ ?_ ?_
  · rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hx : canon x = c := (mem_filter.1 hx).2
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    obtain ⟨t', -, rfl⟩ := mem_image.1 hs'
    simp only at h
    apply Subtype.ext
    simp only
    rw [← hx] at h ⊢
    rw [canon_spec x t, canon_spec x t'] at h
    exact (canon_ker x t t').2 h
  · intro φ _
    simp only [mem_filter, mem_univ, true_and]
    refine Eq.trans ?_ hc
    refine canon_eq_of_ker _ _ fun s t => ?_
    rw [φ.injective.eq_iff, Subtype.mk.injEq]
  · intro x hx
    have hx : canon x = c := (mem_filter.1 hx).2
    funext t
    show x (c t) = x t
    rw [← hx]
    exact canon_spec x t
  · intro φ _
    apply Function.Embedding.ext
    rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    show φ ⟨c (c t), hmem (c t)⟩ = φ ⟨c t, hs⟩
    congr 2
    exact hcc t

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} (w : List (Letter d))
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
/-! ## Invariance under relabelling -/
omit [Fintype α] [Fintype β] in
lemma Es_comp (c : Fin (w.length + 1) → β) (φ : β → α) (i : Fin d) :
    Es w (φ ∘ c) i = (Es w c i).image (Prod.map φ φ) := by
  simp only [Es, image_image]
  refine image_congr fun t _ => ?_
  simp [edge_map]

omit [Fintype β] in
lemma Es_range (c : Fin (w.length + 1) → β) (i : Fin d) (p : β × β) (hp : p ∈ Es w c i) :
    p.1 ∈ Set.range c ∧ p.2 ∈ Set.range c := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 hp
  rcases edge_cases (w.get t) (c t.castSucc) (c t.succ) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} (w : List (Letter d))
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable (c : Fin (w.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} (w : List (Letter d)) {α : Type*} [DecidableEq α]
/-! ## The bounds on the invariants -/
lemma sum_card_Es_le (x : Fin (w.length + 1) → α) : ∑ i, (Es w x i).card ≤ w.length := by
  calc ∑ i, (Es w x i).card
      ≤ ∑ i, (univ.filter fun t : Fin w.length => lab (w.get t) = some i).card :=
        sum_le_sum fun i _ => card_image_le
    _ = (univ.biUnion fun i => univ.filter fun t : Fin w.length => lab (w.get t) = some i).card := by
        rw [card_biUnion]
        intro i _ j _ hij
        show Disjoint _ _
        rw [disjoint_filter]
        intro t _ hi hj
        exact hij (Option.some.inj (hi.symm.trans hj))
    _ ≤ w.length := (card_le_univ _).trans (Fintype.card_fin _).le

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
/-! ## Several closed walks -/
/-- Positions of the closed walks. -/
abbrev Pos := Σ k : ι, Fin ((u k).length + 1)

/-- Number of positions. -/
def nP : ℕ := Fintype.card (Pos u)

/-- An enumeration of the positions. -/
def eP : Pos u ≃ Fin (nP u) := Fintype.equivFin _

/-- The `k`-th walk of a labelling of the positions. -/
def cmp {α : Type*} (x : Fin (nP u) → α) (k : ι) : Fin ((u k).length + 1) → α :=
  fun j => x (eP u ⟨k, j⟩)

/-- All edges of label `i`. -/
def EsM {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) (i : Fin d) : Finset (α × α) :=
  univ.biUnion fun k => Es (u k) (cmp u x k) i

/-- Every walk is closed. -/
def ClM {α : Type*} (x : Fin (nP u) → α) : Prop :=
  ∀ k, cmp u x k 0 = cmp u x k (Fin.last _)

/-- Every walk stands still at `none`. -/
def ConsM {α : Type*} (x : Fin (nP u) → α) : Prop :=
  ∀ k, Cons (u k) (cmp u x k)

/-- Good labellings. -/
def GoodM {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) : Prop :=
  ConsM u x ∧ (∀ i, PInj (EsM u x i)) ∧ ClM u x

instance {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) : Decidable (ClM u x) := by
  unfold ClM; infer_instance

instance {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) : Decidable (ConsM u x) := by
  unfold ConsM; infer_instance

instance {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (nP u) → α) :
    Decidable (GoodM u x) := by
  unfold GoodM; infer_instance

/-- `σ` realises all walks. -/
def RzM {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (nP u) → Fin N) : Prop :=
  ∀ k, Rz (u k) σ (cmp u x k)

instance {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (nP u) → Fin N) :
    Decidable (RzM u σ x) := by
  unfold RzM; infer_instance

/-- The weight. -/
def GM (N : ℕ) {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (nP u) → α) : ℕ :=
  if GoodM u x then ∏ i, (N - (EsM u x i).card).factorial else 0

lemma prod_fixCount_eq {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    ∏ k, fixCount (wordPerm σ (u k)) =
      (univ.filter fun x : Fin (nP u) → Fin N => RzM u σ x ∧ ClM u x).card := by
  have hk : ∀ k, fixCount (wordPerm σ (u k)) =
      (univ.filter fun y : Fin ((u k).length + 1) → Fin N =>
        Rz (u k) σ y ∧ y 0 = y (Fin.last _)).card := fun k => fixCount_eq (u k) σ
  rw [prod_congr rfl (fun k _ => hk k), ← Fintype.card_piFinset]
  symm
  refine card_bij' (fun x _ => fun k => cmp u x k)
    (fun y _ => fun v => y ((eP u).symm v).1 ((eP u).symm v).2) ?_ ?_ ?_ ?_
  · intro x hx
    have hx := (mem_filter.1 hx).2
    rw [Fintype.mem_piFinset]
    exact fun k => mem_filter.2 ⟨mem_univ _, hx.1 k, hx.2 k⟩
  · intro y hy
    rw [Fintype.mem_piFinset] at hy
    have : ∀ k, cmp u (fun v => y ((eP u).symm v).1 ((eP u).symm v).2) k = y k := by
      intro k; funext j; simp only [cmp]; rw [Equiv.symm_apply_apply]
    refine mem_filter.2 ⟨mem_univ _, fun k => ?_, fun k => ?_⟩
    · rw [this]; exact (mem_filter.1 (hy k)).2.1
    · show cmp u _ k 0 = cmp u _ k _
      rw [this]; exact (mem_filter.1 (hy k)).2.2
  · intro x _
    funext v
    simp only [cmp]
    rw [Sigma.eta, Equiv.apply_symm_apply]
  · intro y _
    funext k j
    simp only [cmp]
    rw [Equiv.symm_apply_apply]

lemma RzM_iff {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (nP u) → Fin N) :
    RzM u σ x ↔ ConsM u x ∧ ∀ i, ∀ p ∈ EsM u x i, σ i p.1 = p.2 := by
  constructor
  · intro h
    refine ⟨fun k => ((Rz_iff (u k) σ _).1 (h k)).1, fun i p hp => ?_⟩
    obtain ⟨k, -, hk⟩ := mem_biUnion.1 hp
    exact ((Rz_iff (u k) σ _).1 (h k)).2 i p hk
  · rintro ⟨h1, h2⟩ k
    exact (Rz_iff (u k) σ _).2 ⟨h1 k, fun i p hp =>
      h2 i p (mem_biUnion.2 ⟨k, mem_univ _, hp⟩)⟩

lemma card_RzM {N : ℕ} (x : Fin (nP u) → Fin N) :
    (univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => RzM u σ x).card =
      if ConsM u x then
        ∏ i, (if PInj (EsM u x i) then (N - (EsM u x i).card).factorial else 0)
      else 0 := by
  split_ifs with hc
  · have : (univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => RzM u σ x) =
        Fintype.piFinset (fun i => univ.filter fun τ : Equiv.Perm (Fin N) =>
          ∀ p ∈ EsM u x i, τ p.1 = p.2) := by
      ext σ; simp [RzM_iff, hc, Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset]
    refine prod_congr rfl fun i _ => ?_
    rw [card_ext, Fintype.card_fin]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro σ _ h
    exact hc ((RzM_iff u σ x).1 h).1

lemma sum_prod_fixCount (N : ℕ) :
    ∑ σ : Fin d → Equiv.Perm (Fin N), ∏ k, fixCount (wordPerm σ (u k)) =
      ∑ x : Fin (nP u) → Fin N, GM u N x := by
  simp only [prod_fixCount_eq, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← card_filter]
  by_cases hcl : ClM u x
  · simp only [hcl, and_true]
    rw [card_RzM, GM]
    by_cases hg : GoodM u x
    · rw [if_pos hg, if_pos hg.1]
      exact prod_congr rfl fun i _ => if_pos (hg.2.1 i)
    · rw [if_neg hg]
      split_ifs with hc
      · have : ¬ ∀ i, PInj (EsM u x i) := fun h => hg ⟨hc, h, hcl⟩
        push Not at this
        obtain ⟨i, hi⟩ := this
        exact prod_eq_zero (mem_univ i) (if_neg hi)
      · rfl
  · simp only [hcl, and_false, GM]
    rw [if_neg (fun h => hcl h.2.2)]
    simp

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
omit [Fintype α] [Fintype β] in
lemma EsM_comp (c : Fin (nP u) → β) (φ : β → α) (i : Fin d) :
    EsM u (φ ∘ c) i = (EsM u c i).image (Prod.map φ φ) := by
  unfold EsM
  rw [biUnion_image]
  refine biUnion_congr rfl fun k _ => ?_
  exact Es_comp (u k) (cmp u c k) φ i

omit [Fintype β] in
lemma EsM_range (c : Fin (nP u) → β) (i : Fin d) (p : β × β) (hp : p ∈ EsM u c i) :
    p.1 ∈ Set.range c ∧ p.2 ∈ Set.range c := by
  obtain ⟨k, -, hk⟩ := mem_biUnion.1 hp
  have h := Es_range (u k) (cmp u c k) i p hk
  obtain ⟨⟨j1, hj1⟩, ⟨j2, hj2⟩⟩ := h
  exact ⟨⟨_, hj1⟩, ⟨_, hj2⟩⟩

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable (c : Fin (nP u) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ
omit [Fintype α] [Fintype β] in
lemma card_EsM_comp (i : Fin d) : (EsM u (φ ∘ c) i).card = (EsM u c i).card := by
  rw [EsM_comp]
  refine card_image_of_injOn fun p hp q hq hpq => ?_
  have hp' := EsM_range u c i p hp
  have hq' := EsM_range u c i q hq
  simp only [Prod.map, Prod.mk.injEq] at hpq
  exact Prod.ext (hφ hp'.1 hq'.1 hpq.1) (hφ hp'.2 hq'.2 hpq.2)

omit [Fintype α] [Fintype β] in
lemma goodM_comp : GoodM u (φ ∘ c) ↔ GoodM u c := by
  have key : ∀ s t, φ (c s) = φ (c t) ↔ c s = c t := fun s t =>
    hφ.eq_iff ⟨s, rfl⟩ ⟨t, rfl⟩
  have hP : ∀ i, PInj (EsM u (φ ∘ c) i) ↔ PInj (EsM u c i) := by
    intro i
    rw [EsM_comp]
    unfold PInj
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Prod.map_fst,
      Prod.map_snd]
    refine forall₂_congr fun p hp => forall₂_congr fun q hq => ?_
    have hp' := EsM_range u c i p hp
    have hq' := EsM_range u c i q hq
    rw [hφ.eq_iff hp'.1 hq'.1, hφ.eq_iff hp'.2 hq'.2]
  unfold GoodM ConsM ClM Cons cmp
  simp only [Function.comp, key, hP]

lemma GM_comp (N : ℕ) : GM u N (φ ∘ c) = GM u N c := by
  unfold GM
  simp only [goodM_comp u c φ hφ, card_EsM_comp u c φ hφ]

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {α : Type*} [DecidableEq α]
lemma sum_card_EsM_le (x : Fin (nP u) → α) : ∑ i, (EsM u x i).card ≤ ∑ k, (u k).length := by
  calc ∑ i, (EsM u x i).card ≤ ∑ i, ∑ k, (Es (u k) (cmp u x k) i).card :=
        sum_le_sum fun i _ => card_biUnion_le
    _ = ∑ k, ∑ i, (Es (u k) (cmp u x k) i).card := sum_comm
    _ ≤ ∑ k, (u k).length := sum_le_sum fun k _ => sum_card_Es_le (u k) _

/-! ## Walks read along `ℤ` -/
lemma emod_nn (j : ℤ) {n : ℕ} (hn : 0 < n) : 0 ≤ j % (n : ℤ) := Int.emod_nonneg _ (by omega)

lemma emod_lt (j : ℤ) {n : ℕ} (hn : 0 < n) : j % (n : ℤ) < n := Int.emod_lt_of_pos _ (by omega)

lemma toNat_emod (j : ℤ) {n : ℕ} (hn : 0 < n) : ((j % (n : ℤ)).toNat : ℤ) = j % n :=
  Int.toNat_of_nonneg (emod_nn j hn)

lemma toNat_emod_lt (j : ℤ) {n : ℕ} (hn : 0 < n) : (j % (n : ℤ)).toNat < n := by
  have := emod_lt j hn; have := emod_nn j hn; omega

/-- Walk `k` of a labelling, read periodically along `ℤ`. -/
def W (x : Fin (nP u) → α) (k : ι) (j : ℤ) : α :=
  cmp u x k ⟨min (j % ((u k).length : ℤ)).toNat (u k).length,
    Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The letter of step `j` of walk `k`. -/
def Al (k : ι) (j : ℤ) : Letter d := (u k).getD (j % ((u k).length : ℤ)).toNat none

lemma W_eq_of_val (x : Fin (nP u) → α) (k : ι) (j : ℤ) (jj : Fin ((u k).length + 1))
    (h : min (j % ((u k).length : ℤ)).toNat (u k).length = jj.val) :
    W u x k j = cmp u x k jj := by
  unfold W; congr 1; exact Fin.ext h

lemma W_mem (x : Fin (nP u) → α) (k : ι) (j : ℤ) : W u x k j ∈ univ.image x :=
  mem_image_of_mem _ (mem_univ _)

lemma W_mod (x : Fin (nP u) → α) (k : ι) {j j' : ℤ}
    (h : j % ((u k).length : ℤ) = j' % ((u k).length : ℤ)) : W u x k j = W u x k j' := by
  unfold W; simp only [h]

lemma Al_mod (k : ι) {j j' : ℤ}
    (h : j % ((u k).length : ℤ) = j' % ((u k).length : ℤ)) : Al u k j = Al u k j' := by
  unfold Al; rw [h]

lemma W_fin (x : Fin (nP u) → α) (hcl : ClM u x) (k : ι) (jj : Fin ((u k).length + 1)) :
    W u x k (jj.val : ℤ) = cmp u x k jj := by
  rcases Nat.lt_or_ge jj.val (u k).length with h | h
  · apply W_eq_of_val
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    simp; omega
  · have hj : jj = Fin.last _ := Fin.ext (by simp; omega)
    subst hj
    rw [← hcl k]
    apply W_eq_of_val
    simp

lemma Al_val (k : ι) (n : ℕ) (hn : n < (u k).length) : Al u k n = (u k).get ⟨n, hn⟩ := by
  unfold Al
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  simp [List.getElem?_eq_getElem hn]

lemma step (x : Fin (nP u) → α) (hcl : ClM u x) (k : ι) (hL : 0 < (u k).length) (j : ℤ) :
    ∃ t : Fin (u k).length, W u x k j = cmp u x k t.castSucc ∧
      W u x k (j + 1) = cmp u x k t.succ ∧ Al u k j = (u k).get t := by
  have h1 := toNat_emod j hL
  have h2 := toNat_emod_lt j hL
  refine ⟨⟨(j % ((u k).length : ℤ)).toNat, h2⟩, ?_, ?_, ?_⟩
  · apply W_eq_of_val; simp; omega
  · have : W u x k (j + 1) = W u x k (((j % ((u k).length : ℤ)).toNat + 1 : ℕ) : ℤ) := by
      apply W_mod
      push_cast
      rw [h1, Int.emod_add_emod]
    rw [this]
    exact W_fin u x hcl k (Fin.succ ⟨(j % ((u k).length : ℤ)).toNat, h2⟩)
  · rw [show Al u k j = Al u k ((j % ((u k).length : ℤ)).toNat : ℕ) from Al_mod u k (by rw [h1, Int.emod_emod_of_dvd _ (dvd_refl _)])]
    exact Al_val u k _ h2

lemma mem_EsM_iff (x : Fin (nP u) → α) (hcl : ClM u x) (hL : ∀ k, 0 < (u k).length)
    (i : Fin d) (p : α × α) :
    p ∈ EsM u x i ↔ ∃ k, ∃ j : ℤ, lab (Al u k j) = some i ∧
      edge (Al u k j) (W u x k j) (W u x k (j + 1)) = p := by
  constructor
  · intro hp
    obtain ⟨k, -, hk⟩ := mem_biUnion.1 hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hk
    have ht := (mem_filter.1 ht).2
    refine ⟨k, t.val, ?_, ?_⟩
    · rw [Al_val u k t.val t.2]; exact ht
    · rw [Al_val u k t.val t.2]
      have e1 := W_fin u x hcl k t.castSucc
      have e2 := W_fin u x hcl k t.succ
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at e1 e2
      rw [e1, e2]
  · rintro ⟨k, j, hl, rfl⟩
    obtain ⟨t, e1, e2, e3⟩ := step u x hcl k (hL k) j
    rw [e1, e2, e3]
    rw [e3] at hl
    exact mem_biUnion.2 ⟨k, mem_univ _, mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hl⟩, rfl⟩⟩

/-! ## Half-edges and degrees -/
/-- The used half-edges: `(z, l)` means that a step with letter `l` leaves `z` along an edge. -/
def Hs (x : Fin (nP u) → α) : Finset (α × Letter d) :=
  univ.biUnion fun i => (EsM u x i).image (fun p => (p.2, some (Sum.inl i))) ∪
    (EsM u x i).image (fun p => (p.1, some (Sum.inr i)))

lemma letterInv_letterInv (l : Letter d) : letterInv (letterInv l) = l := by
  rcases l with _ | i | i <;> rfl

lemma letterInv_ne_self {l : Letter d} (h : l ≠ none) : letterInv l ≠ l := by
  rcases l with _ | i | i <;> simp_all [letterInv]

lemma card_Hs (x : Fin (nP u) → α) (hP : ∀ i, PInj (EsM u x i)) :
    (Hs u x).card = 2 * ∑ i, (EsM u x i).card := by
  unfold Hs
  rw [card_biUnion, mul_sum]
  · refine sum_congr rfl fun i _ => ?_
    rw [card_union_of_disjoint]
    · rw [card_image_of_injOn, card_image_of_injOn]
      · ring
      · intro p hp q hq h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 ((hP i p hp q hq).1 h.1)
      · intro p hp q hq h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext ((hP i p hp q hq).2 h.1) h.1
    · rw [disjoint_left]
      intro z h1 h2
      obtain ⟨p, -, rfl⟩ := mem_image.1 h1
      obtain ⟨q, -, h⟩ := mem_image.1 h2
      simp at h
  · intro i _ j _ hij
    rw [Function.onFun, disjoint_left]
    intro z h1 h2
    rcases mem_union.1 h1 with h1 | h1 <;> rcases mem_union.1 h2 with h2 | h2 <;>
    · obtain ⟨p, -, rfl⟩ := mem_image.1 h1
      obtain ⟨q, -, h⟩ := mem_image.1 h2
      simp only [Prod.mk.injEq, Option.some.injEq, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, and_false] at h
      all_goals exact hij h.2.symm

lemma Hs_fst (x : Fin (nP u) → α) {z : α} {l : Letter d} (h : (z, l) ∈ Hs u x) :
    z ∈ univ.image x := by
  simp only [Hs, mem_biUnion, mem_univ, true_and, mem_union, mem_image] at h
  obtain ⟨i, ⟨p, hp, hpz⟩ | ⟨p, hp, hpz⟩⟩ := h
  · simp only [Prod.mk.injEq] at hpz
    obtain ⟨-, ⟨j, hj⟩⟩ := EsM_range u x i p hp
    rw [← hpz.1, ← hj]; exact mem_image_of_mem _ (mem_univ _)
  · simp only [Prod.mk.injEq] at hpz
    obtain ⟨⟨j, hj⟩, -⟩ := EsM_range u x i p hp
    rw [← hpz.1, ← hj]; exact mem_image_of_mem _ (mem_univ _)

lemma mem_Hs_step (x : Fin (nP u) → α) (hcl : ClM u x) (hL : ∀ k, 0 < (u k).length)
    (k : ι) (j : ℤ) (hn : Al u k j ≠ none) :
    (W u x k j, Al u k j) ∈ Hs u x ∧ (W u x k (j + 1), letterInv (Al u k j)) ∈ Hs u x := by
  have hmem : ∀ i, lab (Al u k j) = some i →
      edge (Al u k j) (W u x k j) (W u x k (j + 1)) ∈ EsM u x i :=
    fun i hi => (mem_EsM_iff u x hcl hL i _).2 ⟨k, j, hi, rfl⟩
  generalize Al u k j = l at hmem hn
  rcases l with _ | i | i
  · exact absurd rfl hn
  · have h := hmem i rfl
    simp only [edge] at h
    constructor
    · exact mem_biUnion.2 ⟨i, mem_univ _, mem_union_left _ (mem_image.2 ⟨_, h, rfl⟩)⟩
    · exact mem_biUnion.2 ⟨i, mem_univ _, mem_union_right _ (mem_image.2 ⟨_, h, rfl⟩)⟩
  · have h := hmem i rfl
    simp only [edge] at h
    constructor
    · exact mem_biUnion.2 ⟨i, mem_univ _, mem_union_right _ (mem_image.2 ⟨_, h, rfl⟩)⟩
    · exact mem_biUnion.2 ⟨i, mem_univ _, mem_union_left _ (mem_image.2 ⟨_, h, rfl⟩)⟩

lemma Hs_desc (x : Fin (nP u) → α) (hcl : ClM u x) (hL : ∀ k, 0 < (u k).length)
    {z : α} {l : Letter d} (h : (z, l) ∈ Hs u x) :
    ∃ k, ∃ j : ℤ, W u x k j = z ∧ (l = Al u k j ∨ l = letterInv (Al u k (j - 1))) := by
  simp only [Hs, mem_biUnion, mem_univ, true_and, mem_union, mem_image] at h
  obtain ⟨i, ⟨p, hp, hpz⟩ | ⟨p, hp, hpz⟩⟩ := h
  · simp only [Prod.mk.injEq] at hpz
    obtain ⟨k, j, hl, rfl⟩ := (mem_EsM_iff u x hcl hL i p).1 hp
    obtain ⟨rfl, rfl⟩ := hpz
    generalize ha : Al u k j = a at hl
    rcases a with _ | i' | i' <;> simp only [lab, reduceCtorEq, Option.some.injEq] at hl
    · subst hl
      exact ⟨k, j, by simp [edge], Or.inl ha.symm⟩
    · subst hl
      refine ⟨k, j + 1, by simp [edge], Or.inr ?_⟩
      rw [add_sub_cancel_right, ha]; rfl
  · simp only [Prod.mk.injEq] at hpz
    obtain ⟨k, j, hl, rfl⟩ := (mem_EsM_iff u x hcl hL i p).1 hp
    obtain ⟨rfl, rfl⟩ := hpz
    generalize ha : Al u k j = a at hl
    rcases a with _ | i' | i' <;> simp only [lab, reduceCtorEq, Option.some.injEq] at hl
    · subst hl
      refine ⟨k, j + 1, by simp [edge], Or.inr ?_⟩
      rw [add_sub_cancel_right, ha]; rfl
    · subst hl
      exact ⟨k, j, by simp [edge], Or.inl ha.symm⟩

/-- The degree of `z`: the number of used half-edges at `z`. -/
def deg (x : Fin (nP u) → α) (z : α) : ℕ := ((Hs u x).filter (fun p => p.1 = z)).card

lemma sum_deg (x : Fin (nP u) → α) :
    (Hs u x).card = ∑ z ∈ univ.image x, deg u x z := by
  unfold deg
  exact card_eq_sum_card_fiberwise (fun p hp => Hs_fst u x (z := p.1) (l := p.2) hp)

/-- The standing hypotheses on the walks. -/
structure WH : Prop where
  len : ∀ k, 0 < (u k).length
  nn : ∀ k j, Al u k j ≠ none
  cr : ∀ k j, Al u k (j + 1) ≠ letterInv (Al u k j)

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {α : Type*} [DecidableEq α]
variable {u}
lemma two_le_deg (hw : WH u) (x : Fin (nP u) → α) (hcl : ClM u x) (k : ι) (j : ℤ) :
    2 ≤ deg u x (W u x k j) := by
  have h1 := (mem_Hs_step u x hcl hw.len k j (hw.nn k j)).1
  have h2 := (mem_Hs_step u x hcl hw.len k (j - 1) (hw.nn k (j - 1))).2
  rw [sub_add_cancel] at h2
  have hne : Al u k j ≠ letterInv (Al u k (j - 1)) := by
    have := hw.cr k (j - 1); rwa [sub_add_cancel] at this
  unfold deg
  have hsub : ({(W u x k j, Al u k j), (W u x k j, letterInv (Al u k (j - 1)))} :
      Finset (α × Letter d)) ⊆ (Hs u x).filter (fun p => p.1 = W u x k j) := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact mem_filter.2 ⟨h1, rfl⟩
    · exact mem_filter.2 ⟨h2, rfl⟩
  have := card_le_card hsub
  rw [card_pair (by simpa using hne)] at this
  exact this

lemma two_le_deg' (hw : WH u) (x : Fin (nP u) → α) (hcl : ClM u x) (z : α)
    (hz : z ∈ univ.image x) : 2 ≤ deg u x z := by
  obtain ⟨q, -, rfl⟩ := mem_image.1 hz
  have hq : x q = W u x ((eP u).symm q).1 (((eP u).symm q).2.val : ℤ) := by
    rw [W_fin u x hcl]
    simp [cmp]
  rw [hq]
  exact two_le_deg hw x hcl _ _

theorem nv_le_e (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x) :
    nv x ≤ ∑ i, (EsM u x i).card := by
  have h1 := card_Hs u x hg.2.1
  rw [sum_deg] at h1
  have h2 : ∑ z ∈ univ.image x, 2 ≤ ∑ z ∈ univ.image x, deg u x z :=
    sum_le_sum fun z hz => two_le_deg' hw x hg.2.2 z hz
  rw [sum_const, smul_eq_mul] at h2
  unfold nv
  omega

theorem deg_le_two (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x)
    (heq : nv x = ∑ i, (EsM u x i).card) : ∀ z ∈ univ.image x, deg u x z ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨z0, hz0, hlt⟩ := hc
  have h1 := card_Hs u x hg.2.1
  rw [sum_deg] at h1
  have h2 : ∑ z ∈ univ.image x, 2 < ∑ z ∈ univ.image x, deg u x z :=
    sum_lt_sum (fun z hz => two_le_deg' hw x hg.2.2 z hz) ⟨z0, hz0, hlt⟩
  rw [sum_const, smul_eq_mul] at h2
  unfold nv at heq
  omega

theorem e_le_nv (x : Fin (nP u) → α) (hP : ∀ i, PInj (EsM u x i))
    (hdeg : ∀ z ∈ univ.image x, deg u x z ≤ 2) : ∑ i, (EsM u x i).card ≤ nv x := by
  have h1 := card_Hs u x hP
  rw [sum_deg] at h1
  have h2 : ∑ z ∈ univ.image x, deg u x z ≤ ∑ z ∈ univ.image x, 2 := sum_le_sum hdeg
  rw [sum_const, smul_eq_mul] at h2
  unfold nv
  omega

lemma three {β : Type*} [DecidableEq β] {S : Finset β} (hS : S.card ≤ 2) {a b c : β}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b) (hcb : c ≠ b) : c = a := by
  by_contra hca
  have hsub : ({a, b, c} : Finset β) ⊆ S := by
    intro y hy; simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hab, Ne.symm hca]),
    card_pair (Ne.symm hcb)] at this
  omega

/-! ## Determinism and lockstep -/
lemma edge_iff (l : Letter d) {a b a' b' : α} (h : a = a' ↔ b = b') :
    (edge l a b).1 = (edge l a' b').1 ↔ (edge l a b).2 = (edge l a' b').2 := by
  rcases l with _ | i | i <;> simp only [edge] <;> tauto

lemma edge_inv {l : Letter d} (hl : l ≠ none) (a b : α) :
    edge (letterInv l) a b = edge l b a := by
  rcases l with _ | i | i
  · exact absurd rfl hl
  · rfl
  · rfl

lemma lab_inv (l : Letter d) : lab (letterInv l) = lab l := by
  rcases l with _ | i | i <;> rfl

lemma lab_ne_none' {l : Letter d} (h : l ≠ none) : lab l ≠ none := by
  rcases l with _ | i | i <;> simp_all [lab]

lemma pinj_edge {E : Finset (α × α)} (hP : PInj E) (l : Letter d) {a b a' b' : α}
    (hp : edge l a b ∈ E) (hq : edge l a' b' ∈ E) : (a = a' ↔ b = b') := by
  have := hP _ hp _ hq
  rcases l with _ | i | i <;> simp only [edge] at this
  · exact this
  · exact this.symm
  · exact this

lemma step_mem (x : Fin (nP u) → α) (hcl : ClM u x) (hL : ∀ k, 0 < (u k).length)
    (k : ι) (j : ℤ) (i : Fin d) (hi : lab (Al u k j) = some i) :
    edge (Al u k j) (W u x k j) (W u x k (j + 1)) ∈ EsM u x i :=
  (mem_EsM_iff u x hcl hL i _).2 ⟨k, j, hi, rfl⟩

lemma det (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x) (k k' : ι) (j j' : ℤ)
    (hA : Al u k j = Al u k' j') :
    W u x k j = W u x k' j' ↔ W u x k (j + 1) = W u x k' (j' + 1) := by
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (lab_ne_none' (hw.nn k j))
  have hp := step_mem x hg.2.2 hw.len k j i hi
  have hq := step_mem x hg.2.2 hw.len k' j' i (hA ▸ hi)
  rw [← hA] at hq
  exact pinj_edge (hg.2.1 i) _ hp hq

lemma det_iter (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x) (k k' : ι) (j j' : ℤ)
    (hA : ∀ i : ℕ, Al u k (j + i) = Al u k' (j' + i)) :
    ∀ n : ℕ, (W u x k j = W u x k' j' ↔ W u x k (j + n) = W u x k' (j' + n)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, det hw x hg k k' _ _ (hA n)]
    push_cast
    simp only [add_assoc]

lemma fwd (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x)
    (hdeg : ∀ z ∈ univ.image x, deg u x z ≤ 2) (k k' : ι) (j j' : ℤ)
    (hW : W u x k j = W u x k' j') (hA : Al u k j = Al u k' j') :
    ∀ n : ℕ, W u x k (j + n) = W u x k' (j' + n) ∧ Al u k (j + n) = Al u k' (j' + n) := by
  intro n
  induction n with
  | zero => simpa using ⟨hW, hA⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e1 : W u x k (j + n + 1) = W u x k' (j' + n + 1) := (det hw x hg k k' _ _ ih2).1 ih1
    have hcl := hg.2.2
    have m1 := (mem_Hs_step u x hcl hw.len k (j + n + 1) (hw.nn _ _)).1
    have m2 := (mem_Hs_step u x hcl hw.len k (j + n) (hw.nn _ _)).2
    have m3 := (mem_Hs_step u x hcl hw.len k' (j' + n + 1) (hw.nn _ _)).1
    rw [← e1] at m3
    have hS := hdeg _ (W_mem u x k (j + n + 1))
    unfold deg at hS
    have := three hS (mem_filter.2 ⟨m1, rfl⟩) (mem_filter.2 ⟨m2, rfl⟩)
      (mem_filter.2 ⟨m3, rfl⟩)
      (by simpa using hw.cr k (j + n))
      (by have := hw.cr k' (j' + n); rw [← ih2] at this; simpa using this)
    simp only [Prod.mk.injEq, true_and] at this
    push_cast
    simp only [← add_assoc]
    exact ⟨e1, this.symm⟩

lemma bwd (hw : WH u) (x : Fin (nP u) → α) (hg : GoodM u x)
    (hdeg : ∀ z ∈ univ.image x, deg u x z ≤ 2) (k k' : ι) (j j' : ℤ)
    (hW : W u x k j = W u x k' j') (hA : Al u k' j' = letterInv (Al u k (j - 1))) :
    ∀ n : ℕ, W u x k (j - n) = W u x k' (j' + n) ∧
      Al u k' (j' + n) = letterInv (Al u k (j - 1 - n)) := by
  intro n
  induction n with
  | zero => simpa using ⟨hW, hA⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hcl := hg.2.2
    set a0 := j - 1 - (n : ℤ) with ha0
    have q1 : a0 + 1 = j - n := by rw [ha0]; ring
    have q2 : j - ((n + 1 : ℕ) : ℤ) = a0 := by rw [ha0]; push_cast; ring
    have q3 : j' + ((n + 1 : ℕ) : ℤ) = j' + n + 1 := by push_cast; ring
    have q4 : j - 1 - ((n + 1 : ℕ) : ℤ) = a0 - 1 := by rw [ha0]; push_cast; ring
    rw [q2, q3, q4]
    have hl := hw.nn k a0
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (lab_ne_none' hl)
    have hp := step_mem x hcl hw.len k a0 i hi
    have hq := step_mem x hcl hw.len k' (j' + n) i (by rw [ih2, lab_inv]; exact hi)
    rw [ih2, edge_inv hl] at hq
    have e1 : W u x k a0 = W u x k' (j' + n + 1) :=
      (pinj_edge (hg.2.1 i) _ hp hq).2 (by rw [q1]; exact ih1)
    have m1 := (mem_Hs_step u x hcl hw.len k a0 hl).1
    have m2 := (mem_Hs_step u x hcl hw.len k (a0 - 1) (hw.nn _ _)).2
    rw [sub_add_cancel] at m2
    have m3 := (mem_Hs_step u x hcl hw.len k' (j' + n + 1) (hw.nn _ _)).1
    rw [← e1] at m3
    have hS := hdeg _ (W_mem u x k a0)
    unfold deg at hS
    have := three hS (mem_filter.2 ⟨m2, rfl⟩) (mem_filter.2 ⟨m1, rfl⟩)
      (mem_filter.2 ⟨m3, rfl⟩) ?_ ?_
    · simp only [Prod.mk.injEq, true_and] at this
      exact ⟨e1, this⟩
    · have := hw.cr k (a0 - 1)
      rw [sub_add_cancel] at this
      simpa using (Ne.symm this)
    · have := hw.cr k' (j' + n)
      rw [ih2, letterInv_letterInv] at this
      simpa using this

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {d : ℕ} (r : List (Letter d))
/-! ## Powers of a cyclically reduced non-power -/
/-- The letters of `r`, read periodically along `ℤ`. -/
def R (j : ℤ) : Letter d := r.getD (j % (r.length : ℤ)).toNat none

lemma R_congr {j j' : ℤ} (h : j ≡ j' [ZMOD (r.length : ℤ)]) : R r j = R r j' := by
  unfold R; rw [show j % (r.length : ℤ) = j' % (r.length : ℤ) from h]

lemma R_add_mul (j q : ℤ) : R r (j + q * r.length) = R r j :=
  R_congr r (Int.add_mul_emod_self_right j q _)

lemma R_natCast (n : ℕ) : R r n = r.getD (n % r.length) none := by
  unfold R; rw [← Int.natCast_mod, Int.toNat_natCast]

lemma length_powList' (k : ℕ) : (powList r k).length = k * r.length := by
  simp [powList, List.length_flatten, List.map_replicate, List.sum_replicate]

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {d : ℕ} (r : List (Letter d))
variable {r}
lemma R_ne_none (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none) (j : ℤ) : R r j ≠ none := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  unfold R
  have h := toNat_emod_lt j hℓ
  rw [List.getD_eq_getElem _ _ h]
  exact hnone _ (List.getElem_mem h)

lemma R_cr (hr : r ≠ []) (hcyc : CycRed r) (j : ℤ) : R r (j + 1) ≠ letterInv (R r j) := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have h := toNat_emod_lt j hℓ
  have key := hcyc ⟨(j % (r.length : ℤ)).toNat, h⟩
  simp only [List.get_eq_getElem] at key
  have e1 : R r j = r[(j % (r.length : ℤ)).toNat] := by
    unfold R; rw [List.getD_eq_getElem _ _ h]
  have e2 : R r (j + 1) = r[((j % (r.length : ℤ)).toNat + 1) % r.length]'(Nat.mod_lt _ hℓ) := by
    rw [R_congr r (j' := ((((j % (r.length : ℤ)).toNat + 1) % r.length : ℕ) : ℤ)), R_natCast,
      Nat.mod_mod, List.getD_eq_getElem _ _ (Nat.mod_lt _ hℓ)]
    show (j + 1) % (r.length : ℤ) = _ % _
    push_cast
    rw [Int.emod_emod_of_dvd _ (dvd_refl _), toNat_emod j hℓ, Int.emod_add_emod]
  rw [e1, e2]; exact key

/-- `r` is primitive: equal shifted letter sequences have congruent shifts. -/
lemma prim (hr : r ≠ []) (hnp : IsNonPower (wordFree r)) (j j' : ℤ)
    (h : ∀ n : ℕ, R r (j + n) = R r (j' + n)) : j ≡ j' [ZMOD (r.length : ℤ)] := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  let f : ℕ → Letter d := fun t => R r t
  have hδc := toNat_emod (j' - j) hℓ
  have hδℓ := toNat_emod_lt (j' - j) hℓ
  set δ := ((j' - j) % (r.length : ℤ)).toNat with hδ
  have hper : N52.PartG.IsPer f δ := by
    intro t
    have := h ((((t : ℤ) - j) % r.length).toNat)
    rw [toNat_emod _ hℓ] at this
    simp only [f]
    push_cast
    rw [R_congr r (j := (t : ℤ)) (j' := j + ((t : ℤ) - j) % r.length), this]
    · apply R_congr
      rw [hδc]
      have h1 := ((Int.mod_modEq ((t : ℤ) - j) r.length).add_left j')
      have h2 := ((Int.mod_modEq (j' - j) r.length).add_left (t : ℤ))
      refine h2.trans ?_
      rw [show (t : ℤ) + (j' - j) = j' + ((t : ℤ) - j) by ring]
      exact h1.symm
    · have h1 := ((Int.mod_modEq ((t : ℤ) - j) r.length).add_left j)
      refine (h1.trans ?_).symm
      ring_nf; rfl
  have hperℓ : N52.PartG.IsPer f r.length := by
    intro t
    simp only [f]
    push_cast
    exact R_congr r (Int.add_emod_right _ _)
  by_cases hδ0 : δ = 0
  · rw [hδ0] at hδc
    exact (Int.modEq_iff_dvd.2 (Int.dvd_of_emod_eq_zero (by simpa using hδc.symm)))
  · exfalso
    have hg := N52.PartG.per_gcd f δ r.length hper hperℓ
    set g := Nat.gcd δ r.length
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgδ : g ≤ δ := Nat.gcd_le_left _ (by omega)
    have hgℓ : g ∣ 1 * r.length := by rw [one_mul]; exact Nat.gcd_dvd_right _ _
    have hfA : ∀ t, f t = N52.PartG.A r (t % r.length) := by
      intro t; simp only [f, R_natCast]; rfl
    have := N52.PartG.per_dvd r hr hnp 1 le_rfl g hg0 hgℓ (by
      intro t ht
      rw [one_mul] at ht
      rw [N52.PartG.A_pow r hr 1 t (by omega),
        N52.PartG.A_pow r hr 1 (t % g) (by have := Nat.mod_lt t hg0; omega), ← hfA, ← hfA]
      have := N52.PartG.per_mul hg (t / g) (t % g)
      rw [Nat.mod_add_div] at this
      exact this)
    have := Nat.le_of_dvd hg0 this
    omega

/-- A cyclically reduced word is not a rotation of its inverse. -/
lemma no_refl (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none) (hcyc : CycRed r) (a b : ℤ)
    (h : ∀ n : ℕ, R r (a + n) = letterInv (R r (b - n))) : False := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hall : ∀ y : ℤ, R r y = letterInv (R r (a + b - y)) := by
    intro y
    have := h (((y - a) % r.length).toNat)
    rw [toNat_emod _ hℓ] at this
    have h1 := (Int.mod_modEq (y - a) r.length).add_left a
    rw [R_congr r (j := y) (j' := a + (y - a) % r.length) (by
      refine (h1.trans ?_).symm; ring_nf; rfl), this]
    congr 1
    apply R_congr
    have h2 := (Int.mod_modEq (y - a) r.length).sub_left b
    refine h2.trans ?_; ring_nf; rfl
  set c := (a + b) % (r.length : ℤ) with hcdef
  have hc0 := emod_nn (a + b) hℓ
  have hcℓ := emod_lt (a + b) hℓ
  have hc : ∀ y, R r y = letterInv (R r (c - y)) := by
    intro y
    rw [hall y]
    congr 1
    apply R_congr
    exact ((Int.mod_modEq (a + b) r.length).sub_right y).symm
  obtain ⟨e, he | he⟩ := Int.even_or_odd' c
  · have := hc e
    rw [show c - e = e by omega] at this
    exact letterInv_ne_self (R_ne_none hr hnone e) this.symm
  · obtain ⟨f, hf | hf⟩ := Nat.even_or_odd' r.length
    · have := hc e
      rw [show c - e = e + 1 by omega] at this
      exact R_cr hr hcyc e (by rw [this, letterInv_letterInv])
    · have := hc (e + f + 1)
      rw [show c - (e + f + 1) = (e + f + 1) + (-1) * (r.length : ℤ) by rw [hf]; push_cast; omega,
        R_add_mul] at this
      exact letterInv_ne_self (R_ne_none hr hnone _) this.symm

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {d : ℕ} (r : List (Letter d))
variable {r}
variable (r) {s : ℕ} (m : Fin s → ℕ)
/-- The walks `r ^ m_t`. -/
def uR : Fin s → List (Letter d) := fun t => powList r (m t)

lemma len_uR (k : Fin s) : (uR r m k).length = m k * r.length := length_powList' r _

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {d : ℕ} (r : List (Letter d))
variable {r}
variable (r) {s : ℕ} (m : Fin s → ℕ)
variable {r m}
lemma Al_uR (hr : r ≠ []) (hm : ∀ t, 1 ≤ m t) (k : Fin s) (j : ℤ) :
    Al (uR r m) k j = R r j := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hL : 0 < (uR r m k).length := by rw [len_uR]; exact Nat.mul_pos (hm k) hℓ
  have hn := toNat_emod_lt j hL
  unfold Al
  rw [show (uR r m k) = (List.replicate (m k) r).flatten from rfl,
    N52.PartG.getD_flat r none hr (m k) _ (by rw [← len_uR r m k]; exact hn)]
  unfold R
  congr 1
  have e : ((((j % ((uR r m k).length : ℤ)).toNat % r.length : ℕ)) : ℤ) =
      ((j % (r.length : ℤ)).toNat : ℤ) := by
    push_cast
    rw [toNat_emod _ hL, toNat_emod _ hℓ]
    exact Int.emod_emod_of_dvd _ ⟨m k, by rw [len_uR]; push_cast; ring⟩
  exact_mod_cast e

lemma WH_uR (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none) (hcyc : CycRed r) (hm : ∀ t, 1 ≤ m t) :
    WH (uR r m) where
  len k := by rw [len_uR]; exact Nat.mul_pos (hm k) (List.length_pos_iff.2 hr)
  nn k j := by rw [Al_uR hr hm]; exact R_ne_none hr hnone j
  cr k j := by rw [Al_uR hr hm, Al_uR hr hm]; exact R_cr hr hcyc j

/-- In a colouring of degree `≤ 2`, a vertex determines the phase modulo `|r|`. -/
theorem phase {α : Type*} [DecidableEq α] (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hnp : IsNonPower (wordFree r)) (hm : ∀ t, 1 ≤ m t)
    (x : Fin (nP (uR r m)) → α) (hg : GoodM (uR r m) x)
    (hdeg : ∀ z ∈ univ.image x, deg (uR r m) x z ≤ 2) (k k' : Fin s) (j j' : ℤ)
    (hW : W (uR r m) x k j = W (uR r m) x k' j') : j ≡ j' [ZMOD (r.length : ℤ)] := by
  have hw := WH_uR hr hnone hcyc hm
  have hcl := hg.2.2
  have m1 := (mem_Hs_step _ x hcl hw.len k j (hw.nn _ _)).1
  have m2 := (mem_Hs_step _ x hcl hw.len k (j - 1) (hw.nn _ _)).2
  rw [sub_add_cancel] at m2
  have m3 := (mem_Hs_step _ x hcl hw.len k' j' (hw.nn _ _)).1
  rw [← hW] at m3
  have hS := hdeg _ (W_mem _ x k j)
  unfold deg at hS
  have hab : Al (uR r m) k j ≠ letterInv (Al (uR r m) k (j - 1)) := by
    have := hw.cr k (j - 1); rwa [sub_add_cancel] at this
  have hor : Al (uR r m) k' j' = Al (uR r m) k j ∨
      Al (uR r m) k' j' = letterInv (Al (uR r m) k (j - 1)) := by
    by_contra hc
    push Not at hc
    have := three hS (mem_filter.2 ⟨m1, rfl⟩) (mem_filter.2 ⟨m2, rfl⟩) (mem_filter.2 ⟨m3, rfl⟩)
      (by simpa using hab) (by simpa using hc.2)
    simp only [Prod.mk.injEq, true_and] at this
    exact hc.1 this
  rcases hor with h1 | h1
  · have := fwd hw x hg hdeg k k' j j' hW h1.symm
    apply prim hr hnp j j'
    intro n
    have := (this n).2
    rwa [Al_uR hr hm, Al_uR hr hm] at this
  · have := bwd hw x hg hdeg k k' j j' hW h1
    exfalso
    apply no_refl hr hnone hcyc j' (j - 1)
    intro n
    have := (this n).2
    rwa [Al_uR hr hm, Al_uR hr hm] at this

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
/-! ## The bijection with the colourings of `g₁ ^ m_t` -/
/-- Canonical good colourings. -/
def CGM {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d)) :
    Finset (Fin (nP u) → Fin (nP u)) :=
  (univ.filter fun c : Fin (nP u) → Fin (nP u) => canon c = c).filter (GoodM u)

lemma nv_canon {n : ℕ} {β : Type*} [DecidableEq β] (y : Fin n → β) : nv (canon y) = nv y := by
  unfold nv
  conv_rhs => rw [← comp_canon y, ← image_image]
  refine (card_image_of_injOn ?_).symm
  intro a ha b hb hab
  simp only [coe_image, coe_univ, Set.image_univ] at ha hb
  exact injOn_canon y ha hb hab

lemma arith (j : ℤ) (M ℓ : ℕ) (hM : 0 < M) (hℓ : 0 < ℓ) :
    (j % ((M * ℓ : ℕ) : ℤ)).toNat / ℓ = ((j / ℓ) % M).toNat ∧
      (j % ((M * ℓ : ℕ) : ℤ)).toNat % ℓ = (j % ℓ).toNat := by
  have hj := Int.mul_ediv_add_emod j ℓ
  have ha := Int.mul_ediv_add_emod (j / ℓ) M
  have hb0 := emod_nn j hℓ
  have hbℓ := emod_lt j hℓ
  have ham0 := emod_nn (j / ℓ) hM
  have hamM := emod_lt (j / ℓ) hM
  have hℓ' : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  have key : j % ((M * ℓ : ℕ) : ℤ) = ℓ * ((j / ℓ) % M) + j % ℓ := by
    have := (Int.ediv_emod_unique (a := j) (b := ((M * ℓ : ℕ) : ℤ))
      (q := (j / ℓ) / M) (r := ℓ * ((j / ℓ) % M) + j % ℓ) (by positivity)).2
      ⟨by push_cast; linear_combination hj + (ℓ : ℤ) * ha, by positivity, by
        push_cast; nlinarith⟩
    exact this.2
  have hn : ((j % ((M * ℓ : ℕ) : ℤ)).toNat : ℤ) = ℓ * ((j / ℓ) % M) + j % ℓ := by
    rw [Int.toNat_of_nonneg (by rw [key]; positivity), key]
  push_cast at hn
  constructor
  · have : (((j % ((M * ℓ : ℕ) : ℤ)).toNat / ℓ : ℕ) : ℤ) = (((j / ℓ) % M).toNat : ℤ) := by
      push_cast
      rw [hn, toNat_emod _ hM, add_comm, Int.add_mul_ediv_left _ _ (by omega),
        Int.ediv_eq_zero_of_lt hb0 hbℓ, zero_add]
    exact_mod_cast this
  · have : (((j % ((M * ℓ : ℕ) : ℤ)).toNat % ℓ : ℕ) : ℤ) = ((j % ℓ).toNat : ℤ) := by
      push_cast
      rw [hn, toNat_emod _ hℓ, add_comm, Int.add_mul_emod_self_left, Int.emod_emod_of_dvd _
        (dvd_refl _)]
    exact_mod_cast this

lemma ediv_succ (j : ℤ) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    (j + 1) / ℓ = if j % ℓ + 1 < ℓ then j / ℓ else j / ℓ + 1 := by
  have hj := Int.mul_ediv_add_emod j ℓ
  have hb0 := emod_nn j hℓ
  have hbℓ := emod_lt j hℓ
  have hℓ' : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  split_ifs with h
  · exact ((Int.ediv_emod_unique hℓ').2 ⟨by linear_combination hj, by omega, h⟩).1
  · have h' : j % (ℓ : ℤ) + 1 = ℓ := by omega
    exact ((Int.ediv_emod_unique (r := 0) hℓ').2 ⟨by linear_combination hj - h', le_refl _,
      hℓ'⟩).1

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {d : ℕ} (r : List (Letter d)) {s : ℕ} (m : Fin s → ℕ)
/-- The one-letter word `g₁`. -/
abbrev l0 : Letter 1 := some (Sum.inl 0)

/-- The walks `g₁ ^ m_t`. -/
def u0 : Fin s → List (Letter 1) := fun t => powList [l0] (m t)

lemma len_u0 (k : Fin s) : (u0 m k).length = m k := by
  rw [u0, length_powList']; simp

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {d : ℕ} (r : List (Letter d)) {s : ℕ} (m : Fin s → ℕ)
variable {m}
lemma Al_u0 (hm : ∀ t, 1 ≤ m t) (k : Fin s) (j : ℤ) : Al (u0 m) k j = l0 := by
  have hL : 0 < (u0 m k).length := by rw [len_u0]; exact hm k
  have hn := toNat_emod_lt j hL
  unfold Al
  rw [show u0 m k = (List.replicate (m k) [l0]).flatten from rfl,
    N52.PartG.getD_flat [l0] none (by simp) (m k) _ (by simpa [len_u0] using hn)]
  simp only [List.length_singleton, Nat.mod_one]
  rfl

lemma WH_u0 (hm : ∀ t, 1 ≤ m t) : WH (u0 m) where
  len k := by rw [len_u0]; exact hm k
  nn k j := by rw [Al_u0 hm]; simp
  cr k j := by rw [Al_u0 hm, Al_u0 hm]; simp [letterInv]

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {d : ℕ} (r : List (Letter d)) {s : ℕ} (m : Fin s → ℕ)
variable {m}
variable {r}
lemma phi_bound (k : Fin s) (a : ℕ) (h : a < (u0 m k).length + 1) :
    a * r.length < (uR r m k).length + 1 := by
  have e1 := len_u0 m k
  have e2 := len_uR r m k
  have h3 : a ≤ m k := by omega
  have := Nat.mul_le_mul_right r.length h3
  omega

lemma psi_bound (k : Fin s) (a : ℕ) (h : a < (uR r m k).length + 1) :
    a / r.length < (u0 m k).length + 1 := by
  have e1 := len_u0 m k
  have e2 := len_uR r m k
  have : a / r.length ≤ m k := Nat.div_le_of_le_mul (by rw [mul_comm]; omega)
  omega

/-- Position `(k, a)` of a `g₁`-walk goes to position `(k, a |r|)`. -/
def phiS (p : Pos (u0 m)) : Pos (uR r m) := ⟨p.1, ⟨p.2.val * r.length, phi_bound p.1 _ p.2.2⟩⟩

def phi (q : Fin (nP (u0 m))) : Fin (nP (uR r m)) := eP (uR r m) (phiS ((eP (u0 m)).symm q))

/-- Position `(k, j)` of an `r`-walk goes to position `(k, ⌊j / |r|⌋)`. -/
def psiS (p : Pos (uR r m)) : Pos (u0 m) := ⟨p.1, ⟨p.2.val / r.length, psi_bound p.1 _ p.2.2⟩⟩

def psi (q : Fin (nP (uR r m))) : Fin (nP (u0 m)) := eP (u0 m) (psiS ((eP (uR r m)).symm q))

/-- The phase `j mod |r|`. -/
def phS (p : Pos (uR r m)) : ℕ := p.2.val % r.length

def ph (q : Fin (nP (uR r m))) : ℕ := phS ((eP (uR r m)).symm q)

/-- The periodic extension of a colouring of the `g₁`-walks. -/
def ext {β : Type*} (c₀ : Fin (nP (u0 m)) → β) : Fin (nP (uR r m)) → β × ℕ :=
  fun q => (c₀ (psi (r := r) q), ph q)

lemma cmp_phi {β : Type*} (c : Fin (nP (uR r m)) → β) (k : Fin s)
    (jj : Fin ((u0 m k).length + 1)) :
    cmp (u0 m) (c ∘ phi) k jj = cmp (uR r m) c k ⟨jj.val * r.length, phi_bound k _ jj.2⟩ := by
  simp only [cmp, Function.comp, phi, Equiv.symm_apply_apply]
  rfl

lemma cmp_ext {β : Type*} (c₀ : Fin (nP (u0 m)) → β) (k : Fin s)
    (jj : Fin ((uR r m k).length + 1)) :
    cmp (uR r m) (ext c₀) k jj = (cmp (u0 m) c₀ k ⟨jj.val / r.length, psi_bound k _ jj.2⟩,
      jj.val % r.length) := by
  simp only [cmp, ext, psi, ph, Equiv.symm_apply_apply]
  rfl

lemma psi_phi (hr : r ≠ []) (q : Fin (nP (u0 m))) : psi (r := r) (phi q) = q := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  simp only [psi, phi, Equiv.symm_apply_apply]
  conv_rhs => rw [← (eP (u0 m)).apply_symm_apply q]
  congr 1
  generalize (eP (u0 m)).symm q = p
  obtain ⟨k, jj⟩ := p
  simp only [psiS, phiS]
  congr 1
  exact Fin.ext (Nat.mul_div_cancel _ hℓ)

lemma ph_phi (q : Fin (nP (u0 m))) : ph (r := r) (phi q) = 0 := by
  unfold ph phi
  rw [Equiv.symm_apply_apply]
  simp [phS, phiS]

lemma ClM_res {β : Type*} (c : Fin (nP (uR r m)) → β) (hcl : ClM (uR r m) c) :
    ClM (u0 m) (c ∘ phi) := by
  intro k
  rw [cmp_phi, cmp_phi]
  convert hcl k using 2 <;> apply Fin.ext <;> simp [len_u0, len_uR]

lemma ClM_ext {β : Type*} (hr : r ≠ []) (c₀ : Fin (nP (u0 m)) → β) (hcl : ClM (u0 m) c₀) :
    ClM (uR r m) (ext (r := r) c₀) := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  intro k
  rw [cmp_ext, cmp_ext]
  refine Prod.ext ?_ ?_
  · convert hcl k using 2 <;> apply Fin.ext <;> simp [len_u0, len_uR, Nat.mul_div_cancel _ hℓ]
  · simp [len_uR]

lemma W_res {β : Type*} [DecidableEq β] (hr : r ≠ []) (hm : ∀ t, 1 ≤ m t)
    (c : Fin (nP (uR r m)) → β) (hcl : ClM (uR r m) c) (k : Fin s) (a : ℤ) :
    W (u0 m) (c ∘ phi) k a = W (uR r m) c k (a * r.length) := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hℓ' : (0 : ℤ) < r.length := by exact_mod_cast hℓ
  have hL : 0 < (u0 m k).length := by rw [len_u0]; exact hm k
  have h1 := toNat_emod_lt a hL
  rw [W_eq_of_val (u0 m) (c ∘ phi) k a ⟨(a % ((u0 m k).length : ℤ)).toNat, by omega⟩
    (by simp; omega), cmp_phi, ← W_fin _ c hcl]
  apply W_mod
  simp only [Fin.val_mk]
  push_cast
  rw [toNat_emod a hL]
  have e1 : ((u0 m k).length : ℤ) = m k := by rw [len_u0]
  have e2 : ((uR r m k).length : ℤ) = r.length * m k := by rw [len_uR]; push_cast; ring
  rw [e1, e2, mul_comm _ (r.length : ℤ), mul_comm a (r.length : ℤ),
    Int.mul_emod_mul_of_pos _ _ hℓ', Int.mul_emod_mul_of_pos _ _ hℓ',
    Int.emod_emod_of_dvd _ (dvd_refl _)]

lemma W_ext {β : Type*} [DecidableEq β] (hr : r ≠ []) (hm : ∀ t, 1 ≤ m t)
    (c₀ : Fin (nP (u0 m)) → β) (k : Fin s) (j : ℤ) :
    W (uR r m) (ext (r := r) c₀) k j =
      (W (u0 m) c₀ k (j / r.length), (j % (r.length : ℤ)).toNat) := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hL : 0 < (uR r m k).length := by rw [len_uR]; exact Nat.mul_pos (hm k) hℓ
  have h1 := toNat_emod_lt j hL
  rw [W_eq_of_val (uR r m) _ k j ⟨(j % ((uR r m k).length : ℤ)).toNat, by omega⟩
    (by simp; omega), cmp_ext]
  have har := arith j (m k) r.length (hm k) hℓ
  rw [← len_uR] at har
  rw [har.2]
  congr 1
  have hL0 : 0 < (u0 m k).length := by rw [len_u0]; exact hm k
  refine (W_eq_of_val (u0 m) c₀ k _ _ ?_).symm
  simp only
  rw [har.1, len_u0]
  have := toNat_emod_lt (j / r.length) (hm k)
  omega

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {d : ℕ} {r : List (Letter d)} {s : ℕ} {m : Fin s → ℕ}
/-! ## Goodness of the restriction and of the extension; the count -/
lemma lab_cases {l l' : Letter d} (hl : l ≠ none) (h : lab l = lab l') :
    l' = l ∨ l' = letterInv l := by
  rcases l with _ | i | i <;> rcases l' with _ | j | j <;> simp_all [lab, letterInv]

theorem good_res {β : Type*} [DecidableEq β] (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hm : ∀ t, 1 ≤ m t) (c : Fin (nP (uR r m)) → β)
    (hg : GoodM (uR r m) c) : GoodM (u0 m) (c ∘ phi) := by
  have hw := WH_uR hr hnone hcyc hm
  have hw0 := WH_u0 hm
  have hcl0 := ClM_res c hg.2.2
  refine ⟨?_, ?_, hcl0⟩
  · intro k t ht
    exfalso
    have := hw0.nn k t.val
    rw [Al_val (u0 m) k t.val t.2] at this
    exact this ht
  · intro i p hp q hq
    obtain ⟨k, a, -, rfl⟩ := (mem_EsM_iff _ _ hcl0 hw0.len i p).1 hp
    obtain ⟨k', a', -, rfl⟩ := (mem_EsM_iff _ _ hcl0 hw0.len i q).1 hq
    rw [Al_u0 hm, Al_u0 hm]
    apply edge_iff
    rw [W_res hr hm c hg.2.2, W_res hr hm c hg.2.2, W_res hr hm c hg.2.2,
      W_res hr hm c hg.2.2]
    have := det_iter hw c hg k k' (a * r.length) (a' * r.length) ?_ r.length
    · rw [this, show (a + 1) * (r.length : ℤ) = a * r.length + r.length by ring,
        show (a' + 1) * (r.length : ℤ) = a' * r.length + r.length by ring]
    · intro i
      simp only [Al_uR hr hm]
      rw [add_comm (a * _), add_comm (a' * _), R_add_mul, R_add_mul]

lemma Y_phase {β : Type*} [DecidableEq β] (hr : r ≠ []) (hm : ∀ t, 1 ≤ m t)
    (c₀ : Fin (nP (u0 m)) → β) {k k' : Fin s} {j j' : ℤ}
    (h : W (uR r m) (ext (r := r) c₀) k j = W (uR r m) (ext (r := r) c₀) k' j') :
    j ≡ j' [ZMOD (r.length : ℤ)] := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  rw [W_ext hr hm, W_ext hr hm, Prod.mk.injEq] at h
  have := congrArg (fun n : ℕ => (n : ℤ)) h.2
  simp only [toNat_emod _ hℓ] at this
  exact this

theorem good_ext {β : Type*} [DecidableEq β] (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hm : ∀ t, 1 ≤ m t) (c₀ : Fin (nP (u0 m)) → β)
    (hg₀ : GoodM (u0 m) c₀) : GoodM (uR r m) (ext (r := r) c₀) := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hw := WH_uR hr hnone hcyc hm
  have hw0 := WH_u0 hm
  have hcl := ClM_ext hr c₀ hg₀.2.2
  have Ydet : ∀ k k' j j', (W (uR r m) (ext (r := r) c₀) k j = W (uR r m) (ext (r := r) c₀) k' j' ↔
      W (uR r m) (ext (r := r) c₀) k (j + 1) = W (uR r m) (ext (r := r) c₀) k' (j' + 1)) := by
    intro k k' j j'
    by_cases hph : j ≡ j' [ZMOD (r.length : ℤ)]
    · rw [W_ext hr hm, W_ext hr hm, W_ext hr hm, W_ext hr hm]
      simp only [Prod.mk.injEq]
      have p1 : (j % (r.length : ℤ)).toNat = (j' % (r.length : ℤ)).toNat := by
        rw [show j % (r.length : ℤ) = j' % (r.length : ℤ) from hph]
      have p2 : ((j + 1) % (r.length : ℤ)).toNat = ((j' + 1) % (r.length : ℤ)).toNat := by
        rw [show (j + 1) % (r.length : ℤ) = (j' + 1) % (r.length : ℤ) from hph.add_right 1]
      simp only [p1, p2, and_true]
      rw [ediv_succ j hℓ, ediv_succ j' hℓ,
        show j' % (r.length : ℤ) = j % (r.length : ℤ) from hph.symm]
      split_ifs
      · exact Iff.rfl
      · exact det hw0 c₀ hg₀ k k' _ _ (by rw [Al_u0 hm, Al_u0 hm])
    · exact iff_of_false (fun h => hph (Y_phase hr hm c₀ h))
        (fun h => hph (Int.ModEq.add_right_cancel' 1 (Y_phase hr hm c₀ h)))
  refine ⟨?_, ?_, hcl⟩
  · intro k t ht
    exfalso
    have := hw.nn k t.val
    rw [Al_val (uR r m) k t.val t.2] at this
    exact this ht
  · intro i p hp q hq
    obtain ⟨k, j, hl, rfl⟩ := (mem_EsM_iff _ _ hcl hw.len i p).1 hp
    obtain ⟨k', j', hl', rfl⟩ := (mem_EsM_iff _ _ hcl hw.len i q).1 hq
    rcases lab_cases (hw.nn k j) (hl.trans hl'.symm) with h | h
    · rw [h]; exact edge_iff _ (Ydet k k' j j')
    · rw [h, edge_inv (hw.nn k j)]
      apply edge_iff
      refine iff_of_false (fun he => ?_) (fun he => ?_)
      · have := Y_phase hr hm c₀ he
        apply hw.cr k' j'
        simp only [Al_uR hr hm] at h ⊢
        rw [h, letterInv_letterInv]
        exact (R_congr r this).symm
      · have := Y_phase hr hm c₀ he
        apply hw.cr k j
        simp only [Al_uR hr hm] at h ⊢
        rw [← h]
        exact R_congr r this

lemma deg_ext {β : Type*} [DecidableEq β] (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hm : ∀ t, 1 ≤ m t) (c₀ : Fin (nP (u0 m)) → β)
    (hg₀ : GoodM (u0 m) c₀) :
    ∀ z ∈ univ.image (ext (r := r) c₀), deg (uR r m) (ext (r := r) c₀) z ≤ 2 := by
  have hℓ : 0 < r.length := List.length_pos_iff.2 hr
  have hw := WH_uR hr hnone hcyc hm
  have hcl := ClM_ext hr c₀ hg₀.2.2
  intro z _
  unfold deg
  have hsub : (Hs (uR r m) (ext (r := r) c₀)).filter (fun p => p.1 = z) ⊆
      {(z, R r (z.2 : ℤ)), (z, letterInv (R r ((z.2 : ℤ) - 1)))} := by
    rintro ⟨z', l⟩ hp'
    obtain ⟨hp, hpz⟩ := mem_filter.1 hp'
    simp only at hpz
    subst hpz
    obtain ⟨k, j, hW, hl⟩ := Hs_desc _ _ hcl hw.len hp
    rw [W_ext hr hm] at hW
    subst hW
    simp only [Al_uR hr hm] at hl
    simp only [mem_insert, mem_singleton, Prod.mk.injEq, true_and]
    rcases hl with rfl | rfl
    · left
      apply R_congr
      rw [toNat_emod j hℓ]
      exact (Int.mod_modEq j _).symm
    · right
      congr 1
      apply R_congr
      rw [toNat_emod j hℓ]
      exact ((Int.mod_modEq j _).sub_right 1).symm
  exact (card_le_card hsub).trans (card_insert_le _ _)

lemma key_iff {β : Type*} [DecidableEq β] (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hnp : IsNonPower (wordFree r)) (hm : ∀ t, 1 ≤ m t)
    (c : Fin (nP (uR r m)) → β) (hg : GoodM (uR r m) c)
    (hdeg : ∀ z ∈ univ.image c, deg (uR r m) c z ≤ 2) (k k' : Fin s) (jj jj' : ℕ) :
    W (uR r m) c k jj = W (uR r m) c k' jj' ↔
      W (uR r m) c k ((jj / r.length * r.length : ℕ) : ℤ) =
        W (uR r m) c k' ((jj' / r.length * r.length : ℕ) : ℤ) ∧
        jj % r.length = jj' % r.length := by
  have hw := WH_uR hr hnone hcyc hm
  have hA : ∀ i : ℕ, Al (uR r m) k (((jj / r.length * r.length : ℕ) : ℤ) + i) =
      Al (uR r m) k' (((jj' / r.length * r.length : ℕ) : ℤ) + i) := by
    intro i
    simp only [Al_uR hr hm]
    push_cast
    rw [add_comm _ (i : ℤ), add_comm _ (i : ℤ), R_add_mul, R_add_mul]
  have hdi := det_iter hw c hg k k' _ _ hA
  have e1 : ((jj / r.length * r.length : ℕ) : ℤ) + ((jj % r.length : ℕ) : ℤ) = jj := by
    exact_mod_cast Nat.div_add_mod' jj r.length
  constructor
  · intro h
    have hp := phase hr hnone hcyc hnp hm c hg hdeg k k' jj jj' h
    have hp' : jj % r.length = jj' % r.length := by
      unfold Int.ModEq at hp; exact_mod_cast hp
    have e2 : ((jj' / r.length * r.length : ℕ) : ℤ) + ((jj % r.length : ℕ) : ℤ) = jj' := by
      rw [hp']; exact_mod_cast Nat.div_add_mod' jj' r.length
    refine ⟨(hdi (jj % r.length)).2 ?_, hp'⟩
    rw [e1, e2]; exact h
  · rintro ⟨h, hp'⟩
    have e2 : ((jj' / r.length * r.length : ℕ) : ℤ) + ((jj % r.length : ℕ) : ℤ) = jj' := by
      rw [hp']; exact_mod_cast Nat.div_add_mod' jj' r.length
    rw [← e1, ← e2]
    exact (hdi _).1 h

lemma c_phi_psi {β : Type*} (c : Fin (nP (uR r m)) → β) (k : Fin s)
    (jj : Fin ((uR r m k).length + 1)) :
    c (phi (psi (r := r) (eP (uR r m) ⟨k, jj⟩))) =
      cmp (uR r m) c k ⟨jj.val / r.length * r.length,
        phi_bound k _ (psi_bound k _ jj.2)⟩ := by
  simp only [psi, phi, Equiv.symm_apply_apply]
  rfl

lemma ph_eP (k : Fin s) (jj : Fin ((uR r m k).length + 1)) :
    ph (r := r) (eP (uR r m) ⟨k, jj⟩) = jj.val % r.length := by
  unfold ph
  rw [Equiv.symm_apply_apply]
  rfl

theorem card_B (hr : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none) (hcyc : CycRed r)
    (hnp : IsNonPower (wordFree r)) (hm : ∀ t, 1 ≤ m t) :
    ((CGM (uR r m)).filter (fun c => nv c = ∑ i, (EsM (uR r m) c i).card)).card =
      (CGM (u0 m)).card := by
  have hw := WH_uR hr hnone hcyc hm
  refine card_bij' (fun c _ => canon (c ∘ phi)) (fun c₀ _ => canon (ext (r := r) c₀))
    ?_ ?_ ?_ ?_
  · intro c hc
    simp only [CGM, mem_filter, mem_univ, true_and] at hc ⊢
    refine ⟨canon_canon _, ?_⟩
    have := goodM_comp (u0 m) (canon (c ∘ phi)) (c ∘ phi) (injOn_canon _)
    rw [comp_canon] at this
    exact this.1 (good_res hr hnone hcyc hm c hc.1.2)
  · intro c₀ hc₀
    simp only [CGM, mem_filter, mem_univ, true_and] at hc₀ ⊢
    have hgy := good_ext hr hnone hcyc hm c₀ hc₀.2
    have := goodM_comp (uR r m) (canon (ext (r := r) c₀)) (ext (r := r) c₀) (injOn_canon _)
    rw [comp_canon] at this
    refine ⟨⟨canon_canon _, this.1 hgy⟩, ?_⟩
    rw [nv_canon]
    have e : ∀ i, (EsM (uR r m) (canon (ext (r := r) c₀)) i).card =
        (EsM (uR r m) (ext (r := r) c₀) i).card := fun i => by
      have := card_EsM_comp (uR r m) (canon (ext (r := r) c₀)) (ext (r := r) c₀)
        (injOn_canon _) i
      rw [comp_canon] at this
      exact this.symm
    simp only [e]
    exact le_antisymm (nv_le_e hw _ hgy)
      (e_le_nv _ hgy.2.1 (deg_ext hr hnone hcyc hm c₀ hc₀.2))
  · intro c hc
    simp only [CGM, mem_filter, mem_univ, true_and] at hc
    obtain ⟨⟨hcan, hg⟩, hve⟩ := hc
    have hdeg := deg_le_two hw c hg hve
    show canon (ext (r := r) (canon (c ∘ phi))) = c
    conv_rhs => rw [← hcan]
    apply canon_eq_of_ker
    intro q q'
    obtain ⟨⟨k, jj⟩, rfl⟩ := (eP (uR r m)).surjective q
    obtain ⟨⟨k', jj'⟩, rfl⟩ := (eP (uR r m)).surjective q'
    simp only [ext, Prod.mk.injEq, canon_ker, Function.comp, c_phi_psi, ph_eP]
    have h1 : ∀ k (jj : Fin ((uR r m k).length + 1)), c (eP (uR r m) ⟨k, jj⟩) =
        W (uR r m) c k (jj.val : ℤ) := fun k jj => (W_fin _ c hg.2.2 k jj).symm
    rw [h1, h1, ← W_fin _ c hg.2.2, ← W_fin _ c hg.2.2]
    exact (key_iff hr hnone hcyc hnp hm c hg hdeg k k' jj jj').symm
  · intro c₀ hc₀
    simp only [CGM, mem_filter, mem_univ, true_and] at hc₀
    show canon (canon (ext (r := r) c₀) ∘ phi) = c₀
    conv_rhs => rw [← hc₀.1]
    apply canon_eq_of_ker
    intro a b
    simp only [Function.comp, canon_ker, ext, Prod.mk.injEq, psi_phi hr, ph_phi, and_true]

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section
namespace StrongConv.Q202L2.PartM
open StrongConv StrongConv.Q202L2
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
/-! ## The expectation formula and the limit -/
theorem expect_eq {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
    (N : ℕ) (hL : ∑ k, (u k).length ≤ N) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ((∏ k, fixCount (wordPerm σ (u k)) : ℕ) : ℝ)) =
      ∑ c ∈ CGM u, (N.descFactorial (nv c) : ℝ) / ∏ i, (N.descFactorial (EsM u c i).card : ℝ) := by
  have h1 : ∑ σ : Fin d → Equiv.Perm (Fin N), ∏ k, fixCount (wordPerm σ (u k)) =
      ∑ c ∈ (univ.filter fun c : Fin (nP u) → Fin (nP u) => canon c = c),
        if GoodM u c then N.descFactorial (nv c) * ∏ i, (N - (EsM u c i).card).factorial
        else 0 := by
    rw [sum_prod_fixCount, ← sum_fiberwise_of_maps_to (s := univ)
      (t := univ.filter fun c : Fin (nP u) → Fin (nP u) => canon c = c)
      (g := canon) (fun x _ => mem_filter.2 ⟨mem_univ _, canon_canon x⟩)]
    refine sum_congr rfl fun c hc => ?_
    have hc := (mem_filter.1 hc).2
    have hG : ∀ x ∈ univ.filter fun x : Fin (nP u) → Fin N => canon x = c,
        GM u N x = GM u N c := by
      intro x hx
      have hx := (mem_filter.1 hx).2
      rw [← hx]
      conv_lhs => rw [← comp_canon x]
      exact GM_comp u (canon x) x (injOn_canon x) N
    rw [sum_congr rfl hG, sum_const, card_fiber c hc, Fintype.card_fin, smul_eq_mul, GM]
    split_ifs <;> simp
  unfold uniformExp
  rw [← Nat.cast_sum, h1, ← sum_filter]
  have hcard : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) = (N.factorial : ℝ) ^ d := by
    simp [Fintype.card_perm]
  rw [hcard, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun c _ => ?_
  have he : ∀ i, (EsM u c i).card ≤ N := fun i =>
    (single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)).trans
      ((sum_card_EsM_le u c).trans hL)
  have hfac : (N.factorial : ℝ) ^ d =
      (∏ i, (N.descFactorial (EsM u c i).card : ℝ)) *
        ∏ i, ((N - (EsM u c i).card).factorial : ℝ) := by
    rw [← prod_mul_distrib,
      show (N.factorial : ℝ) ^ d = ∏ _i : Fin d, (N.factorial : ℝ) by simp]
    refine prod_congr rfl fun i _ => ?_
    rw [← Nat.cast_mul, mul_comm, Nat.factorial_mul_descFactorial (he i)]
  simp only [Nat.cast_mul, Nat.cast_prod]
  rw [hfac, mul_div_mul_right _ _ (prod_ne_zero_iff.2 fun i _ => by positivity)]

/-- The limit: the number of canonical good colourings of the walks `g₁ ^ m_t`. -/
def Fm (s : ℕ) (m : Fin s → ℕ) : ℕ := by
  classical exact if ∀ t, 1 ≤ m t then (CGM (u0 m)).card else 0

lemma deg_u0 {s : ℕ} {m : Fin s → ℕ} {β : Type*} [DecidableEq β] (x : Fin (nP (u0 m)) → β) :
    ∀ z ∈ univ.image x, deg (u0 m) x z ≤ 2 := by
  intro z _
  unfold deg
  have hsub : (Hs (u0 m) x).filter (fun p => p.1 = z) ⊆
      {(z, some (Sum.inl 0)), (z, some (Sum.inr 0))} := by
    rintro ⟨z', l⟩ hp'
    obtain ⟨hp, hpz⟩ := mem_filter.1 hp'
    simp only at hpz
    subst hpz
    simp only [Hs, mem_biUnion, mem_univ, true_and, mem_union, mem_image, Prod.mk.injEq] at hp
    obtain ⟨i, ⟨p, -, -, rfl⟩ | ⟨p, -, -, rfl⟩⟩ := hp
    · simp [Subsingleton.elim i 0]
    · simp [Subsingleton.elim i 0]
  exact (card_le_card hsub).trans (card_insert_le _ _)

theorem Fm_bound (s : ℕ) (m : Fin s → ℕ) :
    (Fm s m : ℝ) ≤ (1 + ∑ t, (m t : ℝ)) ^ (2 * s) := by
  classical
  have h1 : (1 : ℝ) ≤ 1 + ∑ t, (m t : ℝ) := by
    have : (0 : ℝ) ≤ ∑ t, (m t : ℝ) := sum_nonneg fun _ _ => Nat.cast_nonneg _
    linarith
  by_cases hm : ∀ t, 1 ≤ m t
  swap
  · unfold Fm; rw [if_neg hm]; simp only [Nat.cast_zero]; positivity
  unfold Fm
  rw [if_pos hm]
  set N := 1 + ∑ t, m t with hN
  have hL : ∑ k, (u0 m k).length ≤ N := by simp only [len_u0]; omega
  have hE := expect_eq (u0 m) N hL
  have hw0 := WH_u0 hm
  have hterm : ∀ c ∈ CGM (u0 m),
      (N.descFactorial (nv c) : ℝ) / ∏ i, (N.descFactorial (EsM (u0 m) c i).card : ℝ) = 1 := by
    intro c hc
    have hg := (mem_filter.1 hc).2
    have hve : nv c = ∑ i, (EsM (u0 m) c i).card :=
      le_antisymm (nv_le_e hw0 c hg) (e_le_nv c hg.2.1 (deg_u0 c))
    rw [Fin.sum_univ_one] at hve
    rw [Fin.prod_univ_one, hve]
    have : (EsM (u0 m) c 0).card ≤ N := by
      have := (single_le_sum (fun j _ => Nat.zero_le _) (mem_univ (0 : Fin 1))).trans
        ((sum_card_EsM_le (u0 m) c).trans hL)
      exact this
    have hpos : (0 : ℝ) < N.descFactorial (EsM (u0 m) c 0).card := by
      exact_mod_cast Nat.descFactorial_pos.2 this
    exact div_self hpos.ne'
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul, mul_one] at hE
  rw [← hE]
  have hle : ∀ σ : Fin 1 → Equiv.Perm (Fin N),
      ((∏ k, fixCount (wordPerm σ (u0 m k)) : ℕ) : ℝ) ≤ (N : ℝ) ^ s := by
    intro σ
    have : ∏ k, fixCount (wordPerm σ (u0 m k)) ≤ N ^ s := by
      have := Finset.prod_le_pow_card (s := (univ : Finset (Fin s)))
        (f := fun k => fixCount (wordPerm σ (u0 m k))) (n := N) (fun k _ => by
          unfold fixCount
          exact (card_filter_le _ _).trans (by simp))
      simpa using this
    exact_mod_cast this
  have hE2 : uniformExp (fun σ : Fin 1 → Equiv.Perm (Fin N) =>
      ((∏ k, fixCount (wordPerm σ (u0 m k)) : ℕ) : ℝ)) ≤ (N : ℝ) ^ s := by
    unfold uniformExp
    have hc : (0 : ℝ) < Fintype.card (Fin 1 → Equiv.Perm (Fin N)) := by
      exact_mod_cast Fintype.card_pos
    rw [div_le_iff₀ hc]
    calc ∑ σ, ((∏ k, fixCount (wordPerm σ (u0 m k)) : ℕ) : ℝ)
        ≤ ∑ _σ : Fin 1 → Equiv.Perm (Fin N), (N : ℝ) ^ s := sum_le_sum fun σ _ => hle σ
      _ = (N : ℝ) ^ s * Fintype.card (Fin 1 → Equiv.Perm (Fin N)) := by
        rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]
  refine hE2.trans ?_
  have hNc : (N : ℝ) = 1 + ∑ t, (m t : ℝ) := by rw [hN]; push_cast; ring
  rw [hNc]
  exact pow_le_pow_right₀ h1 (by omega)

theorem multiwalk_limit :
    ∃ F : (s : ℕ) → (Fin s → ℕ) → ℕ,
      (∀ s (m : Fin s → ℕ), (F s m : ℝ) ≤ (1 + ∑ t, (m t : ℝ)) ^ (2 * s)) ∧
      ∀ {d : ℕ} (r : List (Letter d)), r ≠ [] → (∀ l ∈ r, l ≠ none) → CycRed r →
        IsNonPower (wordFree r) → ∀ (s : ℕ) (m : Fin s → ℕ), (∀ t, 1 ≤ m t) →
          Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
              ((∏ t, fixCount (wordPerm σ (powList r (m t))) : ℕ) : ℝ)))
            atTop (𝓝 (F s m : ℝ)) := by
  classical
  refine ⟨Fm, Fm_bound, ?_⟩
  intro d r hr hnone hcyc hnp s m hm
  have hw := WH_uR hr hnone hcyc hm
  have hT : ∀ c ∈ CGM (uR r m), Tendsto (fun N : ℕ =>
      (N.descFactorial (nv c) : ℝ) / ∏ i, (N.descFactorial (EsM (uR r m) c i).card : ℝ)) atTop
      (𝓝 (if nv c = ∑ i, (EsM (uR r m) c i).card then 1 else 0)) := fun c hc =>
    N52.PartM.tendsto_term (nv c) (fun i => (EsM (uR r m) c i).card)
      (nv_le_e hw c (mem_filter.1 hc).2)
  have hsum := tendsto_finsetSum (CGM (uR r m)) hT
  rw [sum_boole, card_B hr hnone hcyc hnp hm] at hsum
  have hF : (Fm s m : ℝ) = ((CGM (u0 m)).card : ℝ) := by
    unfold Fm; rw [if_pos hm]
  rw [hF]
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (∑ k, (uR r m k).length)] with N hN
  exact (expect_eq (uR r m) N hN).symm

end StrongConv.Q202L2.PartM
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L2
open StrongConv
/-! ## Part M: the several-cycle Nica limit (S5) -/
alias multiwalk_limit := StrongConv.Q202L2.PartM.multiwalk_limit

end StrongConv.Q202L2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L2.PartX
open StrongConv StrongConv.Q202L2
/-! ## Part X: Lemma 10.2 -/
/-- The limit function of Part M. -/
def Fm : (s : ℕ) → (Fin s → ℕ) → ℕ := Classical.choose multiwalk_limit

lemma Fm_bound (s : ℕ) (m : Fin s → ℕ) : (Fm s m : ℝ) ≤ (1 + ∑ t, (m t : ℝ)) ^ (2 * s) :=
  (Classical.choose_spec multiwalk_limit).1 s m

lemma Fm_tendsto {d : ℕ} (r : List (Letter d)) (hne : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none)
    (hcyc : CycRed r) (hnp : IsNonPower (wordFree r)) (s : ℕ) (m : Fin s → ℕ)
    (hm : ∀ t, 1 ≤ m t) :
    Tendsto (fun N : ℕ => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ((∏ t, fixCount (wordPerm σ (powList r (m t))) : ℕ) : ℝ)))
      atTop (𝓝 (Fm s m : ℝ)) :=
  (Classical.choose_spec multiwalk_limit).2 r hne hnone hcyc hnp s m hm

lemma chi_eq (π : StableRep) {N : ℕ} (hN : π.N₀ ≤ N) (g : Equiv.Perm (Fin N)) :
    (π.π N g : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace =
      ∑ a ∈ π.φ.support, MvPolynomial.coeff a π.φ *
        (((∏ i : Fin π.r, (xi ((i : ℕ) + 1) g) ^ (a i) : ℕ)) : ℂ) := by
  rw [π.trace_eq N hN g, MvPolynomial.eval_eq']
  push_cast
  rfl

lemma prod_sigma_eq {r : ℕ} (a : Fin r → ℕ) (f : Fin r → ℕ) :
    ∏ t : Fin (∑ i, a i), f ((finSigmaFinEquiv.symm t).1) = ∏ i, f i ^ a i := by
  rw [← Fintype.prod_equiv finSigmaFinEquiv (fun p => f p.1) _ (fun p => by simp),
    Fintype.prod_sigma]
  simp

/-- The exponents `k (i + 1)`, one for each factor of the monomial `a`. -/
def mk (r k : ℕ) (a : Fin r → ℕ) : Fin (∑ i, a i) → ℕ :=
  fun t => k * (((finSigmaFinEquiv.symm t).1 : ℕ) + 1)

/-- The limit `∑_a c_a F(s_a, k(i+1)…)`. -/
def ellK (π : StableRep) (k : ℕ) : ℂ :=
  ∑ a ∈ π.φ.support, MvPolynomial.coeff a π.φ * ((Fm (∑ i, a i) (mk π.r k a) : ℕ) : ℂ)

lemma limit_of_rep (π : StableRep) {d : ℕ} (w r : List (Letter d)) (k : ℕ) (hk : 1 ≤ k)
    (hne : r ≠ []) (hnone : ∀ l ∈ r, l ≠ none) (hcyc : CycRed r) (hnp : IsNonPower (wordFree r))
    (hfix : ∀ (N : ℕ) (σ : Fin d → Equiv.Perm (Fin N)) (j : ℕ),
      xi j (wordPerm σ w) = fixCount (wordPerm σ (powList r (k * j)))) :
    Tendsto (fun N => chiE π N w) atTop (𝓝 (ellK π k)) := by
  have hev : ∀ N, π.N₀ ≤ N → chiE π N w = ∑ a ∈ π.φ.support, MvPolynomial.coeff a π.φ *
      (((uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ((∏ t, fixCount (wordPerm σ (powList r (mk π.r k a t))) : ℕ) : ℝ)) : ℝ)) : ℂ) := by
    intro N hN
    unfold chiE uniformExp
    simp_rw [chi_eq π hN]
    have hp : ∀ (σ : Fin d → Equiv.Perm (Fin N)) (a : Fin π.r →₀ ℕ),
        (∏ i : Fin π.r, (xi ((i : ℕ) + 1) (wordPerm σ w)) ^ (a i) : ℕ) =
          ∏ t, fixCount (wordPerm σ (powList r (mk π.r k a t))) := by
      intro σ a
      rw [← prod_sigma_eq (fun i => a i) (fun i => xi ((i : ℕ) + 1) (wordPerm σ w))]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [hfix]
      rfl
    simp_rw [hp]
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.mul_sum, mul_div_assoc]
    push_cast
    rfl
  have hlim : Tendsto (fun N : ℕ => ∑ a ∈ π.φ.support, MvPolynomial.coeff a π.φ *
      (((uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ((∏ t, fixCount (wordPerm σ (powList r (mk π.r k a t))) : ℕ) : ℝ)) : ℝ)) : ℂ))
      atTop (𝓝 (ellK π k)) := by
    unfold ellK
    refine tendsto_finset_sum _ fun a _ => tendsto_const_nhds.mul ?_
    have := Fm_tendsto r hne hnone hcyc hnp (∑ i, a i) (mk π.r k a) (fun t => by
      unfold mk; exact Nat.mul_pos hk (Nat.succ_pos _))
    exact (Complex.continuous_ofReal.tendsto _).comp this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop π.N₀] with N hN
  exact (hev N hN).symm

lemma letterInv_eq {d : ℕ} (l : Letter d) : letterInv l = N52.letterInv l := by
  rcases l with _ | (i | i) <;> rfl

lemma cycRed_of {d : ℕ} {r : List (Letter d)} (h : N52.CycRed r) : CycRed r := by
  intro t
  rw [letterInv_eq]
  exact h t

lemma isNonPower_conj {d : ℕ} {v : FreeGroup (Fin d)} (hv : IsNonPower v) (h : FreeGroup (Fin d)) :
    IsNonPower (h * v * h⁻¹) := by
  refine ⟨?_, fun x k hk hx => ?_⟩
  · intro h1
    apply hv.1
    have : v = h⁻¹ * (h * v * h⁻¹) * h := by group
    rw [this, h1]; group
  · apply hv.2 (h⁻¹ * x * h) k hk
    rw [show h⁻¹ * x * h = h⁻¹ * x * h⁻¹⁻¹ by rw [inv_inv], conj_pow, ← hx]; group

lemma isNonPower_of {d : ℕ} (i : Fin d) : IsNonPower (FreeGroup.of i) := by
  refine ⟨FreeGroup.of_ne_one i, fun x k hk hx => ?_⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [one_pow] at hx
    exact FreeGroup.of_ne_one i hx
  have := S9.root_length x k hx1
  rw [← hx, FreeGroup.toWord_of] at this
  simp at this
  omega

lemma sum_comp_eval_eq_zero {X : Type*} [Fintype X] [DecidableEq X] {d : ℕ} (i : Fin d)
    (f : X → ℂ) (hf : ∑ x, f x = 0) : ∑ σ : Fin d → X, f (σ i) = 0 := by
  rw [Fintype.sum_equiv (Equiv.piSplitAt i (fun _ => X)) (fun σ => f (σ i)) (fun p => f p.1)
    (fun σ => rfl), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← Finset.smul_sum, hf, smul_zero]

lemma ellK_one (π : StableRep) (hπ : π.NoTrivialSummand) {d : ℕ} (hd : 0 < d) :
    ellK π 1 = 0 := by
  set r₀ : List (Letter d) := [some (Sum.inl ⟨0, hd⟩)] with hr₀
  have hw : wordFree r₀ = FreeGroup.of ⟨0, hd⟩ := by simp [hr₀, wordFree]
  have hne : r₀ ≠ [] := by simp [hr₀]
  have hnone : ∀ l ∈ r₀, l ≠ none := by simp [hr₀]
  have hcyc : CycRed r₀ := by
    intro t
    simp [hr₀, letterInv]
  have hnp : IsNonPower (wordFree r₀) := hw ▸ isNonPower_of _
  have h1 := limit_of_rep π r₀ r₀ 1 le_rfl hne hnone hcyc hnp (fun N σ j =>
    fix_conj' σ r₀ r₀ (wordFree r₀) 1 1 (pow_one _).symm (by group) j)
  have h2 : Tendsto (fun N => chiE π N r₀) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop π.N₀] with N hN
    unfold chiE
    have : ∀ σ : Fin d → Equiv.Perm (Fin N), wordPerm σ r₀ = σ ⟨0, hd⟩ := by
      intro σ; simp [hr₀, wordPerm, letterPerm]
    simp_rw [this]
    rw [sum_comp_eval_eq_zero ⟨0, hd⟩ (fun τ => (π.π N τ : Matrix (Fin (π.dim N))
      (Fin (π.dim N)) ℂ).trace) (avg_trace_zero π hπ N hN), zero_div]
  exact tendsto_nhds_unique h1 h2

lemma d_pos_of_nonPower {d : ℕ} {v : FreeGroup (Fin d)} (hv : IsNonPower v) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    exfalso
    have key : ∀ u : FreeGroup (Fin 0), u = 1 := fun u => by
      induction u using FreeGroup.induction_on with
      | C1 => rfl
      | of i => exact i.elim0
      | inv_of i _ => exact i.elim0
      | mul x y hx hy => rw [hx, hy, one_mul]
    exact hv.1 (key v)
  · exact h

theorem stable_limit (π : StableRep) (hπ : π.NoTrivialSummand) :
    ∃ (c : ℝ) (β : ℕ), ∀ {d : ℕ} (w : List (Letter d)) (v : FreeGroup (Fin d)) (k : ℕ),
      IsNonPower v → 1 ≤ k → wordFree w = v ^ k →
        ∃ ℓ : ℂ, Tendsto (fun N : ℕ => chiE π N w) atTop (𝓝 ℓ) ∧
          ‖ℓ‖ ≤ c * (k : ℝ) ^ β ∧ (k = 1 → ℓ = 0) := by
  set B : (Fin π.r →₀ ℕ) → ℝ := fun a =>
    ∑ t : Fin (∑ i, a i), ((((finSigmaFinEquiv.symm t).1 : ℕ) : ℝ) + 1) with hB
  refine ⟨∑ a ∈ π.φ.support, ‖MvPolynomial.coeff a π.φ‖ * (1 + B a) ^ (2 * ∑ i, a i),
    ∑ a ∈ π.φ.support, 2 * ∑ i, a i, ?_⟩
  intro d w v k hv hk hw
  obtain ⟨r, h, hne, hnone, hcyc, hr⟩ := N52.PartW.exists_cyc_rep v hv
  have hnp : IsNonPower (wordFree r) := hr ▸ isNonPower_conj hv h
  refine ⟨ellK π k, limit_of_rep π w r k hk hne hnone (cycRed_of hcyc) hnp
    (fun N σ j => fix_conj' σ w r v h k hw hr j), ?_, ?_⟩
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    unfold ellK
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [norm_mul, Complex.norm_natCast]
    have hB0 : 0 ≤ B a := Finset.sum_nonneg fun _ _ => by positivity
    have hsum : ∑ t, (mk π.r k a t : ℝ) = k * B a := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp [mk]
    have hF := Fm_bound (∑ i, a i) (mk π.r k a)
    rw [hsum] at hF
    have h1 : 1 + (k : ℝ) * B a ≤ k * (1 + B a) := by nlinarith
    have h2 : (1 + (k : ℝ) * B a) ^ (2 * ∑ i, a i) ≤ (k : ℝ) ^ (2 * ∑ i, a i) * (1 + B a) ^ (2 * ∑ i, a i) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 _
    have h3 : (k : ℝ) ^ (2 * ∑ i, a i) ≤ (k : ℝ) ^ (∑ a ∈ π.φ.support, 2 * ∑ i, a i) :=
      pow_le_pow_right₀ hk1 (Finset.single_le_sum (f := fun a : Fin π.r →₀ ℕ => 2 * ∑ i, a i)
        (fun _ _ => Nat.zero_le _) ha)
    have hn := norm_nonneg (MvPolynomial.coeff a π.φ)
    calc ‖MvPolynomial.coeff a π.φ‖ * (Fm (∑ i, a i) (mk π.r k a) : ℝ)
        ≤ ‖MvPolynomial.coeff a π.φ‖ * ((k : ℝ) ^ (2 * ∑ i, a i) * (1 + B a) ^ (2 * ∑ i, a i)) :=
          mul_le_mul_of_nonneg_left (hF.trans h2) hn
      _ ≤ ‖MvPolynomial.coeff a π.φ‖ * ((k : ℝ) ^ (∑ a ∈ π.φ.support, 2 * ∑ i, a i) *
            (1 + B a) ^ (2 * ∑ i, a i)) := by gcongr
      _ = _ := by ring
  · rintro rfl
    exact ellK_one π hπ (d_pos_of_nonPower hv)

end StrongConv.Q202L2.PartX
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L2
open StrongConv
/-! ## Part X: Lemma 10.2 -/

end StrongConv.Q202L2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L2.PartX
open StrongConv StrongConv.Q202L2
open scoped Classical
/-! ## Part X: the moment bound -/
/-- The dimension polynomial `N ↦ φ(N, …, N)`. -/
def dimPoly (π : StableRep) : ℂ[X] := MvPolynomial.aeval (fun _ : Fin π.r => (X : ℂ[X])) π.φ

lemma dim_eq (π : StableRep) {N : ℕ} (hN : π.N₀ ≤ N) :
    (π.dim N : ℂ) = (dimPoly π).eval (N : ℂ) := by
  have h1 := π.trace_eq N hN 1
  have hxi : ∀ j, xi j (1 : Equiv.Perm (Fin N)) = N := by intro j; simp [xi]
  simp only [hxi, map_one] at h1
  rw [dimPoly, ← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply]
  simp only [Polynomial.aeval_X]
  have he : (MvPolynomial.aeval fun _ : Fin π.r => (N : ℂ)) π.φ =
      MvPolynomial.eval (fun _ : Fin π.r => (N : ℂ)) π.φ := rfl
  rw [he, ← h1]
  simp

lemma dim_expansion (π : StableRep) : ∃ e : ℕ → ℝ, ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
    (π.dim N : ℝ) / (N : ℝ) ^ π.alpha = ∑ i ∈ Finset.range (π.alpha + 1), e i / (N : ℝ) ^ i := by
  set p : ℂ[X] := dimPoly π with hp
  have hα : π.alpha = p.natDegree := rfl
  refine ⟨fun i => (p.coeff (π.alpha - i)).re, fun N hN hN1 => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hdim : (π.dim N : ℝ) = ∑ k ∈ Finset.range (π.alpha + 1), (p.coeff k).re * (N : ℝ) ^ k := by
    have h := congrArg Complex.re (dim_eq π hN)
    rw [eval_eq_sum_range, ← hα, Complex.re_sum] at h
    rw [show ((π.dim N : ℂ)).re = (π.dim N : ℝ) by simp] at h
    rw [h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.re_mul_ofReal]
  rw [hdim, Finset.sum_div]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hk' : π.alpha + 1 - 1 - k = π.alpha - k := by omega
  rw [hk']
  show (p.coeff (π.alpha - k)).re * (N : ℝ) ^ (π.alpha - k) / (N : ℝ) ^ π.alpha =
    (p.coeff (π.alpha - k)).re / (N : ℝ) ^ k
  have : (N : ℝ) ^ π.alpha = (N : ℝ) ^ (π.alpha - k) * (N : ℝ) ^ k := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  have : (N : ℝ) ^ k ≠ 0 := by positivity
  have : (N : ℝ) ^ (π.alpha - k) ≠ 0 := by positivity
  field_simp

/-- A polynomial in `N` tending to `0` vanishes. -/
lemma coeff_zero_of_tendsto (α : ℕ) (c : ℕ → ℝ)
    (h : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range (α + 1), c j * (N : ℝ) ^ (α - j)) atTop (𝓝 0)) :
    ∀ j ≤ α, c j = 0 := by
  induction α generalizing c with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_self, pow_zero,
      mul_one] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  | succ α ih =>
    have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hg : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range (α + 1), c j * (N : ℝ) ^ (α - j))
        atTop (𝓝 0) := by
      have h1 := (h.div_atTop hN).sub (tendsto_const_nhds (x := c (α + 1)) |>.div_atTop hN)
      rw [sub_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN1
      have hNne : (N : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
                                    positivity
      rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, add_div, add_sub_cancel_right,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [show α + 1 - j = (α - j) + 1 by omega, pow_succ]
      field_simp
    have hc := ih c hg
    have hlast : c (α + 1) = 0 := by
      have h2 : Tendsto (fun _ : ℕ => c (α + 1)) atTop (𝓝 0) := by
        refine h.congr' ?_
        filter_upwards with N
        rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun j hj => by
          rw [hc j (by rw [Finset.mem_range] at hj; omega), zero_mul])]
        simp
      exact tendsto_nhds_unique tendsto_const_nhds h2
    intro j hj
    rcases Nat.lt_or_ge j (α + 1) with h' | h'
    · exact hc j (by omega)
    · rw [show j = α + 1 by omega]; exact hlast

/-- Identification of the coefficients from an exact expansion up to `o(N^{-α})`. -/
lemma nu_eq_of_expansion (π : StableRep) {D d : ℕ} (P : NCPoly D d)
    (ν : ℕ → smoothFun →ₗ[ℝ] ℝ) (h : ℝ[X]) (C : ℝ)
    (hC : ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
      |stE π P N (fun x => h.eval x) -
        ∑ i ∈ Finset.range (π.alpha + 1), ν i (polyFun h) / (N : ℝ) ^ i| ≤
        C / (N : ℝ) ^ (π.alpha + 1))
    (b : ℕ → ℝ) (Sseq : ℕ → ℝ) (S : ℝ) (hS : Tendsto Sseq atTop (𝓝 S))
    (hE : ∀ᶠ N : ℕ in atTop, stE π P N (fun x => h.eval x) =
      ∑ j ∈ Finset.range (π.alpha + 1), b j / (N : ℝ) ^ j + (Sseq N - S) / (N : ℝ) ^ π.alpha) :
    ∀ j ≤ π.alpha, ν j (polyFun h) = b j := by
  set α := π.alpha with hα
  have key := coeff_zero_of_tendsto α (fun j => ν j (polyFun h) - b j) ?_
  · intro j hj
    have := key j hj
    linarith
  set Ex : ℕ → ℝ := fun N => (N : ℝ) ^ α *
    (∑ i ∈ Finset.range (α + 1), ν i (polyFun h) / (N : ℝ) ^ i - stE π P N (fun x => h.eval x))
    with hEx
  have hEx0 : Tendsto Ex atTop (𝓝 0) := by
    have hCN : Tendsto (fun N : ℕ => |C| / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine squeeze_zero_norm' ?_ hCN
    filter_upwards [eventually_ge_atTop (max π.N₀ 1)] with N hN
    have hN0 : π.N₀ ≤ N := le_of_max_le_left hN
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have h1 := hC N hN0 hN1
    rw [abs_sub_comm] at h1
    rw [Real.norm_eq_abs, hEx]
    simp only
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ α)]
    calc (N : ℝ) ^ α * |∑ i ∈ Finset.range (α + 1), ν i (polyFun h) / (N : ℝ) ^ i -
          stE π P N (fun x => h.eval x)|
        ≤ (N : ℝ) ^ α * (C / (N : ℝ) ^ (α + 1)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = C / N := by rw [pow_succ]; field_simp
      _ ≤ |C| / N := by gcongr; exact le_abs_self C
  have hlim := hEx0.add (hS.sub_const S)
  rw [sub_self, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hE, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpow : ∀ j ∈ Finset.range (α + 1), (N : ℝ) ^ α * ((ν j (polyFun h) - b j) / (N : ℝ) ^ j) =
      (ν j (polyFun h) - b j) * (N : ℝ) ^ (α - j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show (N : ℝ) ^ α = (N : ℝ) ^ (α - j) * (N : ℝ) ^ j by rw [← pow_add]; congr 1; omega]
    have : (N : ℝ) ^ j ≠ 0 := by positivity
    field_simp
  rw [← Finset.sum_congr rfl hpow, ← Finset.mul_sum, hEx]
  simp only
  rw [hN]
  simp only [sub_div, Finset.sum_sub_distrib]
  have : (N : ℝ) ^ α ≠ 0 := by positivity
  field_simp
  ring

/-- A word for a free-group element. -/
def wl {d : ℕ} (u : FreeGroup (Fin d)) : List (Letter d) := u.toWord.map N52.PartW.toLetter

lemma wordFree_wl {d : ℕ} (u : FreeGroup (Fin d)) : wordFree (wl u) = u := by
  rw [wl, N52.PartW.wordFree_map_toLetter, FreeGroup.mk_toWord]

lemma chiE_congr (π : StableRep) {d : ℕ} (N : ℕ) {w w' : List (Letter d)}
    (h : wordFree w = wordFree w') : chiE π N w = chiE π N w' := by
  unfold chiE
  simp_rw [wordPerm_eq_lift, h]

/-- The limit of `E[Tr π_N(u(σ))]`. -/
def Glim (π : StableRep) {d : ℕ} (u : FreeGroup (Fin d)) : ℂ :=
  limUnder atTop (fun N => chiE π N (wl u))

/-- The conclusion of Lemma 10.2 with fixed constants. -/
def LimProp (π : StableRep) (c : ℝ) (β : ℕ) : Prop :=
  ∀ {d : ℕ} (w : List (Letter d)) (v : FreeGroup (Fin d)) (k : ℕ),
    IsNonPower v → 1 ≤ k → wordFree w = v ^ k →
      ∃ ℓ : ℂ, Tendsto (fun N : ℕ => chiE π N w) atTop (𝓝 ℓ) ∧
        ‖ℓ‖ ≤ c * (k : ℝ) ^ β ∧ (k = 1 → ℓ = 0)

lemma Glim_facts (π : StableRep) {c : ℝ} {β : ℕ} (hl : LimProp π c β) {d : ℕ}
    (w : List (Letter d)) (v : FreeGroup (Fin d)) (k : ℕ) (hv : IsNonPower v) (hk : 1 ≤ k)
    (hw : wordFree w = v ^ k) :
    Tendsto (fun N => chiE π N w) atTop (𝓝 (Glim π (wordFree w))) ∧
      ‖Glim π (wordFree w)‖ ≤ c * (k : ℝ) ^ β ∧ (k = 1 → Glim π (wordFree w) = 0) := by
  obtain ⟨ℓ, hℓ, hb, h1⟩ := hl w v k hv hk hw
  have hc : ∀ N, chiE π N (wl (wordFree w)) = chiE π N w :=
    fun N => chiE_congr π N (wordFree_wl _)
  have hG : Glim π (wordFree w) = ℓ := by
    unfold Glim
    simp_rw [hc]
    exact hℓ.limUnder_eq
  rw [hG]
  exact ⟨hℓ, hb, h1⟩

lemma Z_eq {d : ℕ} (G : FreeGroup (Fin d) → ℂ) (m : ℕ) (u : FreeGroup (Fin d))
    (hlen : u.toWord.length ≤ m) (h1 : ∀ v, IsNonPower v → u = v → G u = 0) :
    (if u = 1 then 0 else G u) = ∑ k ∈ Finset.Icc 2 m,
      (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ u = v ^ k then G u else 0) := by
  by_cases hu : u = 1
  · rw [if_pos hu]
    symm
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [if_neg]
    rintro ⟨v, hv, h⟩
    have := S9.root_length v k hv.1
    rw [← h, hu] at this
    simp at this
    have := (Finset.mem_Icc.mp hk).1
    omega
  · rw [if_neg hu]
    obtain ⟨v₀, hv₀, hk₀, h₀⟩ := S9.rootExp_spec u hu
    have hk₀m : S9.rootExp u ≤ m := by
      have := S9.root_length v₀ (S9.rootExp u) hv₀.1
      rw [← h₀] at this
      omega
    by_cases h1' : S9.rootExp u = 1
    · rw [h1 v₀ hv₀ (by rw [h₀, h1', pow_one])]
      symm
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk2 := (Finset.mem_Icc.mp hk).1
      rw [if_neg]
      rintro ⟨v, hv, hvk⟩
      have := S9.rootExp_eq u v k hv (by omega) hvk
      omega
    · rw [Finset.sum_eq_single (S9.rootExp u)]
      · rw [if_pos ⟨v₀, hv₀, h₀⟩]
      · intro k hk hne
        rw [if_neg]
        rintro ⟨v, hv, hvk⟩
        exact hne (S9.rootExp_eq u v k hv (by have := (Finset.mem_Icc.mp hk).1; omega) hvk).symm
      · intro hnot
        exfalso
        apply hnot
        rw [Finset.mem_Icc]
        omega

lemma bound_nontriv (π : StableRep) {c : ℝ} {β : ℕ} (hl : LimProp π c β) {d : ℕ}
    (L : S9.Lin d) (D : ℕ) (hD : 1 ≤ D) (hDm : D ≤ L.Dm) (hS : L.Supp D)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ j, ‖S9.Xop L j‖ ≤ R ^ (1 / (L.q : ℝ))) (p : ℕ) (hp : 1 ≤ p) :
    ‖∑ i : Fin (p * L.q) → Letter d, S9.aCoef L D (p * L.q) i *
        (if wordFree (List.ofFn i) = 1 then 0 else Glim π (wordFree (List.ofFn i)))‖ ≤
      |c| * 2 * (L.Dm : ℝ) ^ 12 * (L.q : ℝ) ^ (β + 13) * ((p : ℝ) + 1) ^ (β + 13) * R ^ p := by
  set m := p * L.q with hm
  have hlen : ∀ i : Fin m → Letter d, (wordFree (List.ofFn i)).toWord.length ≤ m := by
    intro i
    have := S9.wordFree_length (List.ofFn i)
    simpa using this
  have hz : ∀ i : Fin m → Letter d,
      (if wordFree (List.ofFn i) = 1 then 0 else Glim π (wordFree (List.ofFn i))) =
      ∑ k ∈ Finset.Icc 2 m, (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ k
        then Glim π (wordFree (List.ofFn i)) else 0) := by
    intro i
    refine Z_eq (Glim π) m _ (hlen i) fun v hv hu => ?_
    exact (Glim_facts π hl (List.ofFn i) v 1 hv le_rfl (by rw [hu, pow_one])).2.2 rfl
  set Gk : ℕ → FreeGroup (Fin d) → ℂ := fun k u =>
    if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ u = v ^ k then Glim π u else 0 with hGk
  have hsplit : ∀ (k : ℕ) (u : FreeGroup (Fin d)),
      (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ u = v ^ k then Glim π u else 0) =
        Gk k u * (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ u = v ^ k then (1 : ℂ) else 0) := by
    intro k u
    simp only [hGk]
    split_ifs <;> simp
  have hB : ∀ k ∈ Finset.Icc 2 m, ∀ u, ‖Gk k u‖ ≤ |c| * (m : ℝ) ^ β := by
    intro k hk u
    have hk2 := (Finset.mem_Icc.mp hk).1
    have hkm := (Finset.mem_Icc.mp hk).2
    simp only [hGk]
    split_ifs with hc
    · obtain ⟨v, hv, hu⟩ := hc
      have := (Glim_facts π hl (wl u) v k hv (by omega) (by rw [wordFree_wl]; exact hu)).2.1
      rw [wordFree_wl] at this
      refine this.trans ?_
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      calc c * (k : ℝ) ^ β ≤ |c| * (k : ℝ) ^ β :=
            mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
        _ ≤ |c| * (m : ℝ) ^ β := by
            gcongr
    · simp only [norm_zero]; positivity
  have hsum : ∑ i : Fin m → Letter d, S9.aCoef L D m i *
        (if wordFree (List.ofFn i) = 1 then 0 else Glim π (wordFree (List.ofFn i))) =
      ∑ k ∈ Finset.Icc 2 m, ∑ i : Fin m → Letter d, S9.aCoef L D m i *
        (Gk k (wordFree (List.ofFn i)) *
          (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ k
            then (1 : ℂ) else 0)) := by
    simp_rw [hz, Finset.mul_sum, hsplit]
    rw [Finset.sum_comm]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.Icc 2 m, ‖∑ i : Fin m → Letter d, S9.aCoef L D m i *
        (Gk k (wordFree (List.ofFn i)) *
          (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ k
            then (1 : ℂ) else 0))‖ ≤
      |c| * (m : ℝ) ^ β * (2 * (L.Dm : ℝ) ^ 12 * ((m : ℝ) + 1) ^ 12 * R ^ p) := by
    intro k hk
    have := S9.PartCore.core_bound_w L D hD hDm hS R hR0 hR p k hp (Finset.mem_Icc.mp hk).1
      (Gk k) (|c| * (m : ℝ) ^ β) (by positivity) (hB k hk)
    simpa [hm] using this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc 2 m).card : ℝ) ≤ m := by
    have : (Finset.Icc 2 m).card ≤ m := by simp
    exact_mod_cast this
  have hq1 : (1 : ℝ) ≤ L.q := by exact_mod_cast L.hq
  have hmq : (m : ℝ) ≤ L.q * ((p : ℝ) + 1) := by
    rw [hm]; push_cast; nlinarith
  have hm1q : (m : ℝ) + 1 ≤ L.q * ((p : ℝ) + 1) := by
    rw [hm]; push_cast; nlinarith
  have hRp : 0 ≤ R ^ p := by positivity
  have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  calc ((Finset.Icc 2 m).card : ℝ) *
        (|c| * (m : ℝ) ^ β * (2 * (L.Dm : ℝ) ^ 12 * ((m : ℝ) + 1) ^ 12 * R ^ p))
      ≤ (m : ℝ) * (|c| * (m : ℝ) ^ β * (2 * (L.Dm : ℝ) ^ 12 * ((m : ℝ) + 1) ^ 12 * R ^ p)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (|c| * 2 * (L.Dm : ℝ) ^ 12 * R ^ p) * ((m : ℝ) ^ (β + 1) * ((m : ℝ) + 1) ^ 12) := by ring
    _ ≤ (|c| * 2 * (L.Dm : ℝ) ^ 12 * R ^ p) *
          ((L.q * ((p : ℝ) + 1)) ^ (β + 1) * (L.q * ((p : ℝ) + 1)) ^ 12) := by
        gcongr
    _ = (|c| * 2 * (L.Dm : ℝ) ^ 12 * R ^ p) * (L.q * ((p : ℝ) + 1)) ^ (β + 13) := by
        rw [← pow_add]
    _ = _ := by rw [mul_pow]; ring

lemma trace_fin_zero (n : ℕ)
    (Y : PiLp 2 (fun _ : Fin 0 => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin 0 => EuclideanSpace ℂ (Fin n))) :
    LinearMap.trace ℂ _ Y = 0 := by
  rw [show Y = 0 from LinearMap.ext fun x => PiLp.ext fun i => i.elim0, map_zero]

theorem stable_moment_bound (π : StableRep) (hπ : π.NoTrivialSummand)
    {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (ν : ℕ → smoothFun →ₗ[ℝ] ℝ)
    (hexp : ∀ h : ℝ[X], ∃ C : ℝ, ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
      |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
            ((fnCalc (fun x => h.eval x) (P.eval (π.model σ)) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
            (N : ℝ) ^ π.alpha) -
        ∑ i ∈ Finset.range (π.alpha + 1), ν i (polyFun h) / (N : ℝ) ^ i| ≤
        C / (N : ℝ) ^ (π.alpha + 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (K0 : ℝ) (s : ℕ), 0 ≤ K0 ∧ ∀ i ≤ π.alpha, ∀ p : ℕ, 1 ≤ p →
      |ν i (polyFun (X ^ p))| ≤ K0 * ((p : ℝ) + 1) ^ s * (‖P.eval (sLimit d)‖ + ε) ^ p := by
  have hexp' : ∀ h : ℝ[X], ∃ C : ℝ, ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
      |stE π P N (fun x => h.eval x) -
        ∑ i ∈ Finset.range (π.alpha + 1), ν i (polyFun h) / (N : ℝ) ^ i| ≤
        C / (N : ℝ) ^ (π.alpha + 1) := hexp
  set R := ‖P.eval (sLimit d)‖ + ε with hR
  have hR0 : 0 ≤ R := by positivity
  have hpoweq : ∀ (p N : ℕ), stE π P N (fun x => (X ^ p : ℝ[X]).eval x) =
      stE π P N (fun x => x ^ p) := by
    intro p N; congr 1; funext x; simp
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0
    refine ⟨0, 0, le_rfl, fun i hi p hp => ?_⟩
    obtain ⟨C, hC⟩ := hexp' (X ^ p)
    have hzero : ∀ N, stE π P N (fun x => (X ^ p : ℝ[X]).eval x) = 0 := by
      intro N
      unfold stE uniformExp
      simp [trace_fin_zero]
    have := nu_eq_of_expansion π P ν (X ^ p) C hC (fun _ => 0) (fun _ => 0) 0
      tendsto_const_nhds (Eventually.of_forall fun N => by rw [hzero]; simp) i hi
    rw [this]; simp
  obtain ⟨L, hDm, hS, hnorm, hlin⟩ := stable_linearization π P hP hD ε hε
  obtain ⟨c, β, hl⟩ := stable_limit π hπ
  obtain ⟨e, he⟩ := dim_expansion π
  set E := ∑ j ∈ Finset.range (π.alpha + 1), |e j| with hEdef
  refine ⟨D * L.Dm * E + D * (|c| * 2 * (L.Dm : ℝ) ^ 12 * (L.q : ℝ) ^ (β + 13)), β + 13,
    by positivity, ?_⟩
  intro j hj p hp
  obtain ⟨C, hC⟩ := hexp' (X ^ p)
  set m := p * L.q with hm
  set T₁ : ℂ := ∑ i : Fin m → Letter d, S9.aCoef L D m i *
    (if wordFree (List.ofFn i) = 1 then (1 : ℂ) else 0) with hT₁
  set Ssum : ℕ → ℂ := fun N => ∑ i : Fin m → Letter d, (D : ℂ) * S9.aCoef L D m i *
    (if wordFree (List.ofFn i) = 1 then 0 else chiE π N (List.ofFn i)) with hSsum
  set Z : ℂ := ∑ i : Fin m → Letter d, S9.aCoef L D m i *
    (if wordFree (List.ofFn i) = 1 then 0 else Glim π (wordFree (List.ofFn i))) with hZ
  set S : ℂ := (D : ℂ) * Z with hSdef
  have hSlim : Tendsto Ssum atTop (𝓝 S) := by
    have hS' : S = ∑ i : Fin m → Letter d, (D : ℂ) * S9.aCoef L D m i *
        (if wordFree (List.ofFn i) = 1 then 0 else Glim π (wordFree (List.ofFn i))) := by
      rw [hSdef, hZ, Finset.mul_sum]
      simp_rw [mul_assoc]
    rw [hS']
    refine tendsto_finset_sum _ fun i _ => tendsto_const_nhds.mul ?_
    split_ifs with h1
    · exact tendsto_const_nhds
    · obtain ⟨v, hv, hk, hu⟩ := S9.rootExp_spec _ h1
      exact (Glim_facts π hl (List.ofFn i) v _ hv hk hu).1
  have hsplit : ∀ N, ∑ i : Fin m → Letter d, (D : ℂ) * S9.aCoef L D m i * chiE π N (List.ofFn i) =
      (D : ℂ) * (π.dim N : ℂ) * T₁ + Ssum N := by
    intro N
    simp only [hSsum, hT₁, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h1
    · rw [chiE_trivial π N _ h1]; ring
    · ring
  set b : ℕ → ℝ := fun j => D * T₁.re * e j + (if j = π.alpha then S.re else 0) with hbdef
  have hb : ∀ N : ℕ, ∑ j ∈ Finset.range (π.alpha + 1), b j / (N : ℝ) ^ j =
      D * T₁.re * ∑ j ∈ Finset.range (π.alpha + 1), e j / (N : ℝ) ^ j +
        S.re / (N : ℝ) ^ π.alpha := by
    intro N
    have h2 : S.re / (N : ℝ) ^ π.alpha = ∑ j ∈ Finset.range (π.alpha + 1),
        (if j = π.alpha then S.re / (N : ℝ) ^ j else 0) := by
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.2 (Nat.lt_succ_self _))]
    rw [Finset.mul_sum, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hbdef]
    split_ifs <;> ring
  have hE : ∀ᶠ N : ℕ in atTop, stE π P N (fun x => (X ^ p : ℝ[X]).eval x) =
      ∑ j ∈ Finset.range (π.alpha + 1), b j / (N : ℝ) ^ j +
        ((Ssum N).re - S.re) / (N : ℝ) ^ π.alpha := by
    filter_upwards [eventually_ge_atTop (max π.N₀ 1)] with N hN
    have hN0 : π.N₀ ≤ N := le_of_max_le_left hN
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    rw [hpoweq, hlin p N hp hN1, hsplit N, hb N, ← he N hN0 hN1]
    have hre : ((D : ℂ) * (π.dim N : ℂ) * T₁ + Ssum N).re =
        D * T₁.re * π.dim N + (Ssum N).re := by
      rw [Complex.add_re, show (D : ℂ) * (π.dim N : ℂ) = (((D * π.dim N : ℕ) : ℝ) : ℂ) by
        push_cast; rfl, Complex.re_ofReal_mul]
      push_cast; ring
    rw [hre]
    ring
  have hν := nu_eq_of_expansion π P ν (X ^ p) C hC b (fun N => (Ssum N).re) S.re
    ((Complex.continuous_re.tendsto _).comp hSlim) hE j hj
  rw [hν]
  have hT : ‖T₁‖ ≤ (L.Dm : ℝ) * R ^ p := S9.core_bound_one L D hD hDm hS R hR0 hnorm p hp
  have hZb := bound_nontriv π hl L D hD hDm hS R hR0 hnorm p hp
  have hej : |e j| ≤ E := Finset.single_le_sum (f := fun j => |e j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have hSb : |S.re| ≤ D * (|c| * 2 * (L.Dm : ℝ) ^ 12 * (L.q : ℝ) ^ (β + 13) *
      ((p : ℝ) + 1) ^ (β + 13) * R ^ p) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [hSdef, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hZb (Nat.cast_nonneg _)
  have hbj : |b j| ≤ D * |T₁.re| * |e j| + |S.re| := by
    show |D * T₁.re * e j + (if j = π.alpha then S.re else 0)| ≤ _
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) D)]
    refine add_le_add le_rfl ?_
    split_ifs
    · exact le_rfl
    · simp
  have hTre : |T₁.re| ≤ (L.Dm : ℝ) * R ^ p := (Complex.abs_re_le_norm _).trans hT
  have hp1 : (1 : ℝ) ≤ ((p : ℝ) + 1) ^ (β + 13) :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith)
  have hRp : 0 ≤ R ^ p := by positivity
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hDn : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  calc |b j| ≤ D * |T₁.re| * |e j| + |S.re| := hbj
    _ ≤ D * ((L.Dm : ℝ) * R ^ p) * E + D * (|c| * 2 * (L.Dm : ℝ) ^ 12 * (L.q : ℝ) ^ (β + 13) *
          ((p : ℝ) + 1) ^ (β + 13) * R ^ p) := by
        gcongr
    _ ≤ D * ((L.Dm : ℝ) * R ^ p) * E * ((p : ℝ) + 1) ^ (β + 13) +
          D * (|c| * 2 * (L.Dm : ℝ) ^ 12 * (L.q : ℝ) ^ (β + 13) *
          ((p : ℝ) + 1) ^ (β + 13) * R ^ p) := by
        exact add_le_add_left (le_mul_of_one_le_right (by positivity) hp1) _
    _ = _ := by ring

end StrongConv.Q202L2.PartX
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L2
open StrongConv
/-! ## Part X: the moment bound -/
alias stable_moment_bound := StrongConv.Q202L2.PartX.stable_moment_bound

/-! ## Assembly -/
theorem supp_subset_Icc_of_stableExpTr_expansion_dev (π : StableRep) (hπ : π.NoTrivialSummand)
    {D d : ℕ} (hd : 2 ≤ d) (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (ν : ℕ → smoothFun →ₗ[ℝ] ℝ) (hν : ∀ i, IsCSDistribution (ν i))
    (hexp : ∀ h : ℝ[X], ∃ C : ℝ, ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
      |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
            ((fnCalc (fun x => h.eval x) (P.eval (π.model σ)) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
            (N : ℝ) ^ π.alpha) -
        ∑ i ∈ Finset.range (π.alpha + 1), ν i (polyFun h) / (N : ℝ) ^ i| ≤
        C / (N : ℝ) ^ (π.alpha + 1)) :
    ∀ i ≤ π.alpha, supp (ν i) ⊆
      Set.Icc (-‖P.eval (sLimit d)‖) ‖P.eval (sLimit d)‖ := by
  intro i hi
  refine (supp_subset_Icc_limsup (ν i) (hν i)).trans ?_
  set r := limsup (fun p : ℕ => |ν i (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop with hr
  have hρ0 : 0 ≤ ‖P.eval (sLimit d)‖ := norm_nonneg _
  have hle : r ≤ ‖P.eval (sLimit d)‖ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨K0, s, hK0, hb⟩ := stable_moment_bound π hπ P hP ν hexp ε hε
    exact S9.limsup_pow_le (fun p => ν i (polyFun (X ^ p))) K0 s (‖P.eval (sLimit d)‖ + ε)
      (by positivity) hK0 (hb i hi)
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

end StrongConv.Q202L2
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology Finset
noncomputable section

end
end


section
open Polynomial Filter Topology
open StrongConv
theorem solution (π : StableRep) (hπ : π.NoTrivialSummand)
    {D d : ℕ} (hd : 2 ≤ d) (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (ν : ℕ → smoothFun →ₗ[ℝ] ℝ) (hν : ∀ i, IsCSDistribution (ν i))
    (hexp : ∀ h : ℝ[X], ∃ C : ℝ, ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
      |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
            ((fnCalc (fun x => h.eval x) (P.eval (π.model σ)) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
              PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
            (N : ℝ) ^ π.alpha) -
        ∑ i ∈ Finset.range (π.alpha + 1), ν i (polyFun h) / (N : ℝ) ^ i| ≤
        C / (N : ℝ) ^ (π.alpha + 1)) :
    ∀ i ≤ π.alpha, supp (ν i) ⊆
      Set.Icc (-‖P.eval (sLimit d)‖) ‖P.eval (sLimit d)‖ :=
  StrongConv.Q202L2.supp_subset_Icc_of_stableExpTr_expansion_dev π hπ hd P hP ν hν hexp
end
