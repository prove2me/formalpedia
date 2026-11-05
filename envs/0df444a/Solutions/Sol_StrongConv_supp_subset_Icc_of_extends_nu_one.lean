-- Prove2me | solution 1 for StrongConv.supp_subset_Icc_of_extends_nu_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T01:07:07.743912+00:00
-- url     : https://prove2.me/submissions/fe5e2a7e-0c47-4e20-973f-2efcb0af1f22

import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_exists_linearization
import Theorems.Thm_StrongConv_tendsto_mul_uniformExp_trN_wordEval
import Theorems.Thm_StrongConv_tendsto_uniformExp_trN_wordEval
import Theorems.Thm_StrongConv_supp_subset_Icc_limsup
import Mathlib

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

/-- `E[tr_N w(S^N)]`. -/
def fExp (N : ℕ) (w : List (Letter d)) : ℝ :=
  uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w))

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

def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => π x = x).card

lemma permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply, mul_apply_eq_comp]
  rfl

lemma permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

lemma permOpPerp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : OnesPerp N) :
    (permOpPerp π x : EuclideanSpace ℂ (Fin N)) = permOp π x := rfl

lemma permOpPerp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOpPerp (π * ρ) = permOpPerp π * permOpPerp ρ := by
  ext x : 2
  simp [permOpPerp_apply, permOp_mul]

lemma permOpPerp_one {N : ℕ} : permOpPerp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x : 2
  simp [permOpPerp_apply, permOp_one]

lemma inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪permOp π x, y⟫_ℂ = ⟪x, permOp π⁻¹ y⟫_ℂ := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

lemma star_permOpPerp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    star (permOpPerp π) = permOpPerp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, permOpPerp_apply]
  rw [inner_permOp, inv_inv]

lemma wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordEval (sModel σ) w = permOpPerp (wordPerm σ w) := by
  induction w with
  | nil => simp [wordEval, wordPerm, permOpPerp_one]
  | cons a w ih =>
    simp only [wordEval, wordPerm, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, permOpPerp_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [letterPerm, permOpPerp_one]
    · simp [letterPerm, letterOp, sModel]
    · simp [letterPerm, letterOp, sModel, star_permOpPerp]

lemma trace_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) = (fixCount π : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (Fin N)), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr,
    ContinuousLinearMap.coe_coe, permOp_apply]
  rw [fixCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (π.symm i = i) ↔ (π i = i) := by
    rw [Equiv.symm_apply_eq, eq_comm]
  by_cases h : π i = i
  · simp [h, this.mpr h]
  · simp [h, mt this.mp h]

lemma trace_eq_add_of_isCompl {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (p q : Submodule ℂ M) (h : IsCompl p q) (f : M →ₗ[ℂ] M)
    (hp : Set.MapsTo f p p) (hq : Set.MapsTo f q q) :
    LinearMap.trace ℂ M f = LinearMap.trace ℂ p (f.restrict hp) +
      LinearMap.trace ℂ q (f.restrict hq) := by
  let A : Fin 2 → Submodule ℂ M := ![p, q]
  have hA : DirectSum.IsInternal A :=
    (DirectSum.isInternal_submodule_iff_isCompl A (i := 0) (j := 1) (by decide)
      (by ext k; fin_cases k <;> simp)).mpr h
  have hf : ∀ i, Set.MapsTo f (A i) (A i) := by
    intro i; fin_cases i
    · exact hp
    · exact hq
  rw [LinearMap.trace_eq_sum_trace_restrict hA hf, Fin.sum_univ_two]
  rfl

lemma trace_permOpPerp {N : ℕ} (hN : 1 ≤ N) (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) = (fixCount π : ℂ) - 1 := by
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin N)) := ℂ ∙ onesVec N with hK
  have hones : permOp π (onesVec N) = onesVec N := by
    ext j; simp [permOp_apply, onesVec]
  have hp : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) K K := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [ContinuousLinearMap.coe_coe, map_smul, hones]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hq : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) Kᗮ Kᗮ := by
    intro x hx
    exact (permOpPerp π ⟨x, hx⟩).2
  have h := trace_eq_add_of_isCompl K Kᗮ (Submodule.isCompl_orthogonal K)
    _ hp hq
  rw [trace_permOp] at h
  have h1 : LinearMap.restrict _ hp = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    show permOp π (c • onesVec N) = c • onesVec N
    rw [map_smul, hones]
  have h2 : LinearMap.restrict _ hq = ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) := by
    ext x; rfl
  have hne : onesVec N ≠ 0 := by
    intro h0
    have := congr_arg (fun v : EuclideanSpace ℂ (Fin N) => v ⟨0, hN⟩) h0
    simp [onesVec] at this
  have hr : Module.finrank ℂ K = 1 := finrank_span_singleton hne
  rw [h1, h2, LinearMap.trace_id, hr] at h
  rw [h]
  push_cast
  ring

theorem wordPerm_eq_lift {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordPerm σ w = FreeGroup.lift σ (wordFree w) := by
  induction w with
  | nil => simp [wordPerm, wordFree]
  | cons a w ih =>
    simp only [wordPerm, wordFree, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    rcases a with _ | (i | i) <;> simp [letterPerm]

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

theorem transfer (hlim : P.eval (sLimit d) = Tcomp L D (sLimit d)) {N : ℕ}
    (σ : Fin d → Equiv.Perm (Fin N)) :
    P.eval (sModel σ) = Tcomp L D (sModel σ) := by
  have h1 := eval_expand_fiber P L (sLimit d) leftReg (fun w => wordEval_sLimit w)
  have h2 := Tcomp_expand_fiber P L (sLimit d) leftReg (fun w => wordEval_sLimit w)
  have h0 : ∑ h ∈ tIdx P L, tensorOp (CP P h - CB L h) (leftReg h) = 0 := by
    simp_rw [tensorOp_sub_left]
    rw [Finset.sum_sub_distrib, ← h1, ← h2, hlim, sub_self]
  have hc := extract (tIdx P L) (fun h => CP P h - CB L h) h0
  have hPi : ∀ w, wordEval (sModel σ) w = permOpPerp (FreeGroup.lift σ (wordFree w)) := by
    intro w
    rw [wordEval_sModel, wordPerm_eq_lift]
  rw [eval_expand_fiber P L (sModel σ) (fun h => permOpPerp (FreeGroup.lift σ h)) hPi,
    Tcomp_expand_fiber P L (sModel σ) (fun h => permOpPerp (FreeGroup.lift σ h)) hPi]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [sub_eq_zero.mp (hc h hh)]

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

theorem final_alg {ι σ : Type*} [Fintype ι] [Fintype σ] (D N : ℕ) (c : ι → ℂ) (f : ι → σ → ℝ) :
    (∑ s, (∑ i, c i * ((f i s : ℝ) : ℂ)).re / ((D : ℝ) * N)) / (Fintype.card σ : ℝ) =
    (∑ i, ((D : ℂ)⁻¹ * c i) * ((((∑ s, f i s / N) / (Fintype.card σ : ℝ)) : ℝ) : ℂ)).re := by
  have hre : ∀ (i : ι) (r : ℝ), ((D : ℂ)⁻¹ * c i * (r : ℂ)).re = (D : ℝ)⁻¹ * (c i).re * r := by
    intro i r
    have : (D : ℂ)⁻¹ = (((D : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, mul_assoc, mul_comm (c i), ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    simp [mul_assoc]
    left; ring
  rw [Complex.re_sum]
  simp_rw [hre]
  have hl : ∀ s, (∑ i, c i * ((f i s : ℝ) : ℂ)).re = ∑ i, (c i).re * f i s := by
    intro s
    rw [Complex.re_sum]
    simp
  simp_rw [hl]
  simp only [Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  field_simp

theorem trace_wordEval_sModel {d N : ℕ} (hN : 1 ≤ N) (σ : Fin d → Equiv.Perm (Fin N))
    (w : List (Letter d)) :
    LinearMap.trace ℂ (OnesPerp N)
      ((wordEval (sModel σ) w : OnesPerp N →L[ℂ] OnesPerp N) : OnesPerp N →ₗ[ℂ] OnesPerp N) =
      (((fixCount (wordPerm σ w) : ℝ) - 1 : ℝ) : ℂ) := by
  rw [wordEval_sModel, trace_permOpPerp hN]
  push_cast
  ring

theorem linearization_data {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (hD : 1 ≤ D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : Lin d, D ≤ L.Dm ∧ L.Supp D ∧
      (∀ j, ‖Xop L j‖ ≤ (‖P.eval (sLimit d)‖ + ε) ^ (1 / (L.q : ℝ))) ∧
      ∀ p N : ℕ, 1 ≤ p → 1 ≤ N →
        expTr P N (fun x => x ^ p) =
          (∑ i : Fin (p * L.q) → Letter d,
            aCoef L D (p * L.q) i * ((fExp N (List.ofFn i) : ℝ) : ℂ)).re := by
  obtain ⟨q, Dim, A, h1, hq', hq1, heq, hnorm⟩ := StrongConv.exists_linearization P ε hε
  have hDm : D ≤ DmOf q Dim := h1 ▸ Dim_le_DmOf q Dim 1 (by omega)
  have hS1 := mkLin_supp1 q hq1 Dim A D h1
  have hlim := hlim_of q hq1 Dim A P h1 hq' heq
  refine ⟨mkLin q hq1 Dim A, hDm, ⟨hS1, mkLin_supp2 q hq1 Dim A D hq'⟩,
    fun j => Xop_norm_le q hq1 Dim A _ hnorm j, ?_⟩
  intro p N hp hN
  have hT : ∀ σ : Fin d → Equiv.Perm (Fin N),
      trDN D N (fnCalc (fun x => x ^ p) (P.eval (sModel σ))) =
      (∑ i : Fin (p * q) → Letter d, (Bprod (mkLin q hq1 Dim A) (p * q) i).trace *
        (((fixCount (wordPerm σ (List.ofFn i)) : ℝ) - 1 : ℝ) : ℂ)).re / ((D : ℝ) * N) := by
    intro σ
    unfold trDN
    rw [fnCalc_pow _ (eval_isSelfAdjoint P hP _), transfer P (mkLin q hq1 Dim A) hlim σ]
    rw [trace_Tcomp_pow (mkLin q hq1 Dim A) D hDm hS1 (sModel σ) hq1 p hp, trace_XprodU]
    simp only [trace_wordEval_sModel hN]
    rfl
  have hfE : ∀ i : Fin (p * q) → Letter d, fExp N (List.ofFn i) =
      (∑ σ : Fin d → Equiv.Perm (Fin N),
        (((fixCount (wordPerm σ (List.ofFn i)) : ℝ) - 1) / N)) /
        (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) := by
    intro i
    unfold fExp uniformExp
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    unfold trN
    beta_reduce
    rw [trace_wordEval_sModel hN]
    simp
  show expTr P N (fun x => x ^ p) =
    (∑ i : Fin (p * q) → Letter d, aCoef (mkLin q hq1 Dim A) D (p * q) i *
      ((fExp N (List.ofFn i) : ℝ) : ℂ)).re
  unfold expTr uniformExp
  simp_rw [hT]
  simp_rw [aCoef, hfE]
  exact final_alg D N (fun i : Fin (p * q) → Letter d => (Bprod (mkLin q hq1 Dim A) (p * q) i).trace)
    (fun i σ => (fixCount (wordPerm σ (List.ofFn i)) : ℝ) - 1)

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

/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => π x = x).card

/-! ### Copied from S5 PartPerm -/

open scoped InnerProductSpace

lemma permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply, mul_apply_eq_comp]
  rfl

lemma permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

lemma permOpPerp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : OnesPerp N) :
    (permOpPerp π x : EuclideanSpace ℂ (Fin N)) = permOp π x := rfl

lemma permOpPerp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOpPerp (π * ρ) = permOpPerp π * permOpPerp ρ := by
  ext x : 2
  simp [permOpPerp_apply, permOp_mul]

lemma permOpPerp_one {N : ℕ} : permOpPerp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x : 2
  simp [permOpPerp_apply, permOp_one]

lemma inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪permOp π x, y⟫_ℂ = ⟪x, permOp π⁻¹ y⟫_ℂ := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

lemma star_permOpPerp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    star (permOpPerp π) = permOpPerp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, permOpPerp_apply]
  rw [inner_permOp, inv_inv]

lemma wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordEval (sModel σ) w = permOpPerp (wordPerm σ w) := by
  induction w with
  | nil => simp [wordEval, wordPerm, permOpPerp_one]
  | cons a w ih =>
    simp only [wordEval, wordPerm, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, permOpPerp_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [letterPerm, permOpPerp_one]
    · simp [letterPerm, letterOp, sModel]
    · simp [letterPerm, letterOp, sModel, star_permOpPerp]

lemma trace_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) = (fixCount π : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (Fin N)), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr,
    ContinuousLinearMap.coe_coe, permOp_apply]
  rw [fixCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (π.symm i = i) ↔ (π i = i) := by
    rw [Equiv.symm_apply_eq, eq_comm]
  by_cases h : π i = i
  · simp [h, this.mpr h]
  · simp [h, mt this.mp h]

lemma trace_eq_add_of_isCompl {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (p q : Submodule ℂ M) (h : IsCompl p q) (f : M →ₗ[ℂ] M)
    (hp : Set.MapsTo f p p) (hq : Set.MapsTo f q q) :
    LinearMap.trace ℂ M f = LinearMap.trace ℂ p (f.restrict hp) +
      LinearMap.trace ℂ q (f.restrict hq) := by
  let A : Fin 2 → Submodule ℂ M := ![p, q]
  have hA : DirectSum.IsInternal A :=
    (DirectSum.isInternal_submodule_iff_isCompl A (i := 0) (j := 1) (by decide)
      (by ext k; fin_cases k <;> simp)).mpr h
  have hf : ∀ i, Set.MapsTo f (A i) (A i) := by
    intro i; fin_cases i
    · exact hp
    · exact hq
  rw [LinearMap.trace_eq_sum_trace_restrict hA hf, Fin.sum_univ_two]
  rfl

lemma trace_permOpPerp {N : ℕ} (hN : 1 ≤ N) (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) = (fixCount π : ℂ) - 1 := by
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin N)) := ℂ ∙ onesVec N with hK
  have hones : permOp π (onesVec N) = onesVec N := by
    ext j; simp [permOp_apply, onesVec]
  have hp : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) K K := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [ContinuousLinearMap.coe_coe, map_smul, hones]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hq : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) Kᗮ Kᗮ := by
    intro x hx
    exact (permOpPerp π ⟨x, hx⟩).2
  have h := trace_eq_add_of_isCompl K Kᗮ (Submodule.isCompl_orthogonal K)
    _ hp hq
  rw [trace_permOp] at h
  have h1 : LinearMap.restrict _ hp = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    show permOp π (c • onesVec N) = c • onesVec N
    rw [map_smul, hones]
  have h2 : LinearMap.restrict _ hq = ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) := by
    ext x; rfl
  have hne : onesVec N ≠ 0 := by
    intro h0
    have := congr_arg (fun v : EuclideanSpace ℂ (Fin N) => v ⟨0, hN⟩) h0
    simp [onesVec] at this
  have hr : Module.finrank ℂ K = 1 := finrank_span_singleton hne
  rw [h1, h2, LinearMap.trace_id, hr] at h
  rw [h]
  push_cast
  ring

theorem wordPerm_eq_lift {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordPerm σ w = FreeGroup.lift σ (wordFree w) := by
  induction w with
  | nil => simp [wordPerm, wordFree]
  | cons a w ih =>
    simp only [wordPerm, wordFree, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    rcases a with _ | (i | i) <;> simp [letterPerm]

theorem trN_wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    trN N (wordEval (sModel σ) w) = ((fixCount (wordPerm σ w) : ℝ) - 1) / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [trN]
  rw [trN, wordEval_sModel, trace_permOpPerp hN]
  simp

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

theorem tau_wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    tau (wordEval (sLimit d) w) = if wordFree w = 1 then 1 else 0 := by
  classical
  rw [wordEval_sLimit, tau, delta, lp.inner_single_left, leftReg_apply]
  simp only [mul_one, lp.single_apply]
  by_cases h : wordFree w = 1
  · simp [h]
  · rw [if_neg h, Pi.single_apply, if_neg (by simpa [inv_eq_one] using h)]
    simp


/-! ### The pieces -/

lemma rootExp_eq' {d : ℕ} (u v : FreeGroup (Fin d)) (k : ℕ) (hv : IsNonPower v) (hk : 1 ≤ k)
    (h : u = v ^ k) : rootExp u = k := by
  have hu : u ≠ 1 := by
    intro h1
    have hv1 : v ≠ 1 := hv.1
    have := root_length v k hv1
    rw [← h, h1] at this
    simp at this
    omega
  have h2 : ∃ v : FreeGroup (Fin d), ∃ k : ℕ, IsNonPower v ∧ 1 ≤ k ∧ u = v ^ k :=
    root_exists u hu
  unfold rootExp
  rw [dif_pos h2]
  have h3 := Classical.choose_spec h2
  have h4 := Classical.choose_spec h3
  exact root_unique _ v _ k h4.1 hv h4.2.1 hk (h4.2.2.symm.trans h)

lemma fExp_one {d : ℕ} (N : ℕ) (hN : 1 ≤ N) (w : List (Letter d)) (hw : wordFree w = 1) :
    fExp N w = ((N : ℝ) - 1) / N := by
  have h1 : ∀ σ : Fin d → Equiv.Perm (Fin N), trN N (wordEval (sModel σ) w) = ((N : ℝ) - 1) / N := by
    intro σ
    rw [trN_wordEval_sModel, wordPerm_eq_lift, hw, map_one]
    have : fixCount (1 : Equiv.Perm (Fin N)) = N := by
      simp [fixCount]
    rw [this]
  unfold fExp uniformExp
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin d → Equiv.Perm (Fin N)) := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp

lemma ind_tendsto {d : ℕ} (w : List (Letter d)) :
    Tendsto (fun N : ℕ => fExp N w) atTop (𝓝 (if wordFree w = 1 then (1 : ℝ) else 0)) ∧
    Tendsto (fun N : ℕ => (N : ℝ) * (fExp N w - (if wordFree w = 1 then (1 : ℝ) else 0))) atTop
      (𝓝 (if wordFree w = 1 then (-1 : ℝ) else (((rootExp (wordFree w)).divisors.card : ℝ) - 1))) := by
  by_cases hw : wordFree w = 1
  · simp only [hw, if_true]
    constructor
    · have h1 : Tendsto (fun N : ℕ => 1 - 1 / (N : ℝ)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
      rw [sub_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [fExp_one N hN w hw]
      have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      field_simp
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [fExp_one N hN w hw]
      have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      field_simp
      ring
  · simp only [hw, if_false]
    obtain ⟨v, k, hv, hk, hvk⟩ := root_exists (wordFree w) hw
    have hre : rootExp (wordFree w) = k := rootExp_eq' _ v k hv hk hvk
    constructor
    · have h := tendsto_uniformExp_trN_wordEval d w
      rw [tau_wordEval_sLimit, if_neg hw] at h
      have := (Complex.continuous_re.tendsto 0).comp h
      simpa [Function.comp_def, fExp] using this
    · simpa [hre, fExp] using tendsto_mul_uniformExp_trN_wordEval d w hw v k hv hk hvk


theorem nu_one_pow_formula {D d : ℕ} (P : NCPoly D d) (L : Lin d) (p : ℕ) (hp : 1 ≤ p)
    (h1b : ∀ N : ℕ, 1 ≤ N → expTr P N (fun x => x ^ p) =
      (∑ i : Fin (p * L.q) → Letter d,
        aCoef L D (p * L.q) i * ((fExp N (List.ofFn i) : ℝ) : ℂ)).re) :
    nu P 1 (X ^ p) =
      (∑ i : Fin (p * L.q) → Letter d, aCoef L D (p * L.q) i *
        (if wordFree (List.ofFn i) = 1 then (-1 : ℂ)
         else (((rootExp (wordFree (List.ofFn i))).divisors.card : ℝ) - 1 : ℝ))).re := by
  set m := p * L.q with hm
  set a : (Fin m → Letter d) → ℂ := fun i => aCoef L D m i with ha
  set ind : (Fin m → Letter d) → ℝ := fun i => if wordFree (List.ofFn i) = 1 then (1 : ℝ) else 0
    with hind
  set cc : (Fin m → Letter d) → ℝ := fun i =>
    if wordFree (List.ofFn i) = 1 then (-1 : ℝ)
    else (((rootExp (wordFree (List.ofFn i))).divisors.card : ℝ) - 1) with hcc
  set F : ℕ → ℝ := fun N => expTr P N (fun x => x ^ p) with hF
  have hFeq : (fun N => expTr P N (fun x => (X ^ p : ℝ[X]).eval x)) = F := by
    funext N; simp [F]
  set c0 : ℝ := (∑ i, a i * ((ind i : ℝ) : ℂ)).re with hc0
  have hT1 : Tendsto (fun N : ℕ => ∑ i, a i * ((fExp N (List.ofFn i) : ℝ) : ℂ)) atTop
      (𝓝 (∑ i, a i * ((ind i : ℝ) : ℂ))) :=
    tendsto_finsetSum _ fun i _ =>
      tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp (ind_tendsto _).1)
  have hTF : Tendsto F atTop (𝓝 c0) := by
    have := (Complex.continuous_re.tendsto _).comp hT1
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp_apply, F]
    rw [h1b N hN]
  have h0 : asympCoeff F 0 = c0 := by
    rw [asympCoeff]
    simp only [pow_zero, one_mul, Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    exact hTF.limUnder_eq
  have hT2 : Tendsto (fun N : ℕ => ∑ i, a i *
      (((N : ℝ) * (fExp N (List.ofFn i) - ind i) : ℝ) : ℂ)) atTop
      (𝓝 (∑ i, a i * ((cc i : ℝ) : ℂ))) :=
    tendsto_finsetSum _ fun i _ =>
      tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp (ind_tendsto _).2)
  have hT3 := (Complex.continuous_re.tendsto _).comp hT2
  have h1 : asympCoeff F 1 = (∑ i, a i * ((cc i : ℝ) : ℂ)).re := by
    rw [asympCoeff]
    simp only [Fin.sum_univ_one, Fin.val_zero, h0, pow_zero, div_one, pow_one]
    refine Tendsto.limUnder_eq (hT3.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp_apply, F]
    rw [h1b N hN]
    have : ∑ i, a i * (((N : ℝ) * (fExp N (List.ofFn i) - ind i) : ℝ) : ℂ) =
        (N : ℂ) * ((∑ i, a i * ((fExp N (List.ofFn i) : ℝ) : ℂ)) -
          ∑ i, a i * ((ind i : ℝ) : ℂ)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [this]
    have h := Complex.re_ofReal_mul (N : ℝ) ((∑ i, a i * ((fExp N (List.ofFn i) : ℝ) : ℂ)) -
          ∑ i, a i * ((ind i : ℝ) : ℂ))
    rw [Complex.ofReal_natCast] at h
    rw [h, Complex.sub_re]
  show asympCoeff (fun N => expTr P N (fun x => (X ^ p : ℝ[X]).eval x)) 1 = _
  rw [hFeq, h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [cc]
  split_ifs <;> simp

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

theorem core_bound (L : Lin d) (D : ℕ) (hD : 1 ≤ D) (hDm : D ≤ L.Dm) (hS : L.Supp D)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ j, ‖Xop L j‖ ≤ R ^ (1 / (L.q : ℝ))) (p k : ℕ) (hp : 1 ≤ p)
    (hk : 2 ≤ k) :
    ‖∑ i : Fin (p * L.q) → Letter d, aCoef L D (p * L.q) i *
        (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ k
         then (1 : ℂ) else 0)‖ ≤
      2 * (L.Dm : ℝ) ^ 12 * (((p * L.q : ℕ) : ℝ) + 1) ^ 12 * R ^ p := by
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
  have hind : ∀ i : Fin m → Letter d, (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧
      wordFree (List.ofFn i) = v ^ (j + 2) then (1 : ℂ) else 0) =
      ∑ u ∈ U, (if W i = u then (1 : ℂ) else 0) := by
    intro i
    rw [Finset.sum_ite_eq]
    by_cases h : ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ (j + 2)
    · rw [if_pos h, if_pos]
      simp only [hU, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨i, Finset.mem_univ _, rfl⟩, h⟩
    · rw [if_neg h, if_neg]
      intro hmem
      simp only [hU, Finset.mem_filter] at hmem
      exact h hmem.2
  have hsum : ∑ i : Fin m → Letter d, aCoef L D m i * (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧
      wordFree (List.ofFn i) = v ^ (j + 2) then (1 : ℂ) else 0) =
      ∑ u ∈ U, (D : ℂ)⁻¹ * (Fr L 1 m u).trace := by
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
    rw [Finset.mul_sum]
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
  have hnorm : ‖∑ u ∈ U, (D : ℂ)⁻¹ * (Fr L 1 m u).trace‖ ≤ (L.Dm : ℝ) * ∑ u ∈ U, ‖Fr L 1 m u‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    have hDinv : ‖(D : ℂ)⁻¹‖ ≤ 1 := by
      simp only [norm_inv, Complex.norm_natCast]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast hD)
    calc ‖(D : ℂ)⁻¹ * (Fr L 1 m u).trace‖ = ‖(D : ℂ)⁻¹‖ * ‖(Fr L 1 m u).trace‖ := norm_mul _ _
      _ ≤ 1 * ‖(Fr L 1 m u).trace‖ := by gcongr
      _ ≤ L.Dm * ‖Fr L 1 m u‖ := by rw [one_mul]; exact fro_trace L _
  refine hnorm.trans ?_
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
theorem linearization_data {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (hD : 1 ≤ D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : Lin d, D ≤ L.Dm ∧ L.Supp D ∧
      (∀ j, ‖Xop L j‖ ≤ (‖P.eval (sLimit d)‖ + ε) ^ (1 / (L.q : ℝ))) ∧
      ∀ p N : ℕ, 1 ≤ p → 1 ≤ N →
        expTr P N (fun x => x ^ p) =
          (∑ i : Fin (p * L.q) → Letter d,
            aCoef L D (p * L.q) i * ((fExp N (List.ofFn i) : ℝ) : ℂ)).re := PartLin.linearization_data P hP hD ε hε

theorem nu_one_pow_formula {D d : ℕ} (P : NCPoly D d) (L : Lin d) (p : ℕ) (hp : 1 ≤ p)
    (h1b : ∀ N : ℕ, 1 ≤ N → expTr P N (fun x => x ^ p) =
      (∑ i : Fin (p * L.q) → Letter d,
        aCoef L D (p * L.q) i * ((fExp N (List.ofFn i) : ℝ) : ℂ)).re) :
    nu P 1 (X ^ p) =
      (∑ i : Fin (p * L.q) → Letter d, aCoef L D (p * L.q) i *
        (if wordFree (List.ofFn i) = 1 then (-1 : ℂ)
         else (((rootExp (wordFree (List.ofFn i))).divisors.card : ℝ) - 1 : ℝ))).re := PartLim.nu_one_pow_formula P L p hp h1b

theorem core_bound_one (L : Lin d) (D : ℕ) (hD : 1 ≤ D) (hDm : D ≤ L.Dm) (hS : L.Supp D)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ j, ‖Xop L j‖ ≤ R ^ (1 / (L.q : ℝ))) (p : ℕ) (hp : 1 ≤ p) :
    ‖∑ i : Fin (p * L.q) → Letter d, aCoef L D (p * L.q) i *
        (if wordFree (List.ofFn i) = 1 then (1 : ℂ) else 0)‖ ≤ (L.Dm : ℝ) * R ^ p := PartCoreOne.core_bound_one L D hD hDm hS R hR0 hR p hp

theorem core_bound (L : Lin d) (D : ℕ) (hD : 1 ≤ D) (hDm : D ≤ L.Dm) (hS : L.Supp D)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : ∀ j, ‖Xop L j‖ ≤ R ^ (1 / (L.q : ℝ))) (p k : ℕ) (hp : 1 ≤ p)
    (hk : 2 ≤ k) :
    ‖∑ i : Fin (p * L.q) → Letter d, aCoef L D (p * L.q) i *
        (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ k
         then (1 : ℂ) else 0)‖ ≤
      2 * (L.Dm : ℝ) ^ 12 * (((p * L.q : ℕ) : ℝ) + 1) ^ 12 * R ^ p := PartCore.core_bound L D hD hDm hS R hR0 hR p k hp hk

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

/-- The coefficient attached to a word. -/
def cw {d : ℕ} (u : FreeGroup (Fin d)) : ℂ :=
  if u = 1 then (-1 : ℂ) else (((rootExp u).divisors.card : ℝ) - 1 : ℝ)

theorem cw_eq {d : ℕ} (m : ℕ) (u : FreeGroup (Fin d)) (hm : u.toWord.length ≤ m) :
    cw u = -(if u = 1 then (1 : ℂ) else 0) +
      ∑ k ∈ Finset.Icc 2 m, (((k.divisors.card : ℝ) - 1 : ℝ) : ℂ) *
        (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ u = v ^ k then (1 : ℂ) else 0) := by
  by_cases hu : u = 1
  · subst hu
    have : ∀ k ∈ Finset.Icc 2 m, ¬ ∃ v : FreeGroup (Fin d), IsNonPower v ∧ (1 : FreeGroup (Fin d)) = v ^ k := by
      rintro k hk ⟨v, hv, h⟩
      have := root_length v k hv.1
      rw [← h] at this
      simp at this
      have := (Finset.mem_Icc.mp hk).1
      omega
    rw [Finset.sum_eq_zero]
    · simp [cw]
    · intro k hk
      rw [if_neg (this k hk)]; simp
  · obtain ⟨v₀, hv₀, hk₀, h₀⟩ := rootExp_spec u hu
    have hk₀m : rootExp u ≤ m := by
      have := root_length v₀ (rootExp u) hv₀.1
      rw [← h₀] at this
      omega
    simp only [cw, if_neg hu]
    by_cases h1 : rootExp u = 1
    · rw [Finset.sum_eq_zero]
      · simp [h1]
      · intro k hk
        have hk2 := (Finset.mem_Icc.mp hk).1
        rw [if_neg]
        · simp
        · rintro ⟨v, hv, hvk⟩
          have := rootExp_eq u v k hv (by omega) hvk
          omega
    · rw [Finset.sum_eq_single (rootExp u)]
      · rw [if_pos ⟨v₀, hv₀, h₀⟩]; simp
      · intro k hk hne
        rw [if_neg]
        · simp
        · rintro ⟨v, hv, hvk⟩
          exact hne (rootExp_eq u v k hv (by have := (Finset.mem_Icc.mp hk).1; omega) hvk).symm
      · intro hnot
        exfalso
        apply hnot
        rw [Finset.mem_Icc]
        omega


/-! ## The moment bound -/

theorem moment_bound {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) (hD : 1 ≤ D) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (K0 : ℝ) (s : ℕ), 0 ≤ K0 ∧ ∀ p : ℕ, 1 ≤ p →
      |nu P 1 (X ^ p)| ≤ K0 * ((p : ℝ) + 1) ^ s * (‖P.eval (sLimit d)‖ + ε) ^ p := by
  obtain ⟨L, hDm, hS, hnorm, hmodel⟩ := linearization_data P hP hD ε hε
  have hR0 : 0 ≤ ‖P.eval (sLimit d)‖ + ε := by positivity
  set R := ‖P.eval (sLimit d)‖ + ε with hR
  refine ⟨(L.Dm : ℝ) + 2 * (L.Dm : ℝ) ^ 12 * (L.q : ℝ) ^ 14, 14, by positivity, ?_⟩
  intro p hp
  rw [nu_one_pow_formula P L p hp (fun N hN => hmodel p N hp hN)]
  refine (Complex.abs_re_le_norm _).trans ?_
  set m := p * L.q with hm
  have hcw : ∀ i : Fin m → Letter d, (if wordFree (List.ofFn i) = 1 then (-1 : ℂ)
      else (((rootExp (wordFree (List.ofFn i))).divisors.card : ℝ) - 1 : ℝ)) =
      cw (wordFree (List.ofFn i)) := fun i => rfl
  simp_rw [hcw]
  have hlen : ∀ i : Fin m → Letter d, (wordFree (List.ofFn i)).toWord.length ≤ m := by
    intro i
    have := wordFree_length (List.ofFn i)
    simpa using this
  have key : ∑ i : Fin m → Letter d, aCoef L D m i * cw (wordFree (List.ofFn i)) =
      -(∑ i : Fin m → Letter d, aCoef L D m i * (if wordFree (List.ofFn i) = 1 then (1 : ℂ) else 0)) +
      ∑ k ∈ Finset.Icc 2 m, (((k.divisors.card : ℝ) - 1 : ℝ) : ℂ) *
        ∑ i : Fin m → Letter d, aCoef L D m i *
          (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ k
           then (1 : ℂ) else 0) := by
    have h1 : ∀ i : Fin m → Letter d, aCoef L D m i * cw (wordFree (List.ofFn i)) =
        -(aCoef L D m i * (if wordFree (List.ofFn i) = 1 then (1 : ℂ) else 0)) +
        ∑ k ∈ Finset.Icc 2 m, (((k.divisors.card : ℝ) - 1 : ℝ) : ℂ) *
          (aCoef L D m i * (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ k
           then (1 : ℂ) else 0)) := by
      intro i
      rw [cw_eq m _ (hlen i), mul_add, mul_neg, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
  rw [key]
  have hE := core_bound_one L D hD hDm hS R hR0 hnorm p hp
  have hZ : ∀ k ∈ Finset.Icc 2 m, ‖(((k.divisors.card : ℝ) - 1 : ℝ) : ℂ) *
        ∑ i : Fin m → Letter d, aCoef L D m i *
          (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ k
           then (1 : ℂ) else 0)‖ ≤
      (m : ℝ) * (2 * (L.Dm : ℝ) ^ 12 * ((m : ℝ) + 1) ^ 12 * R ^ p) := by
    intro k hk
    have hk2 := (Finset.mem_Icc.mp hk).1
    have hkm := (Finset.mem_Icc.mp hk).2
    rw [norm_mul]
    have hcore := core_bound L D hD hDm hS R hR0 hnorm p k hp hk2
    have hω : ‖(((k.divisors.card : ℝ) - 1 : ℝ) : ℂ)‖ ≤ m := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 : (1 : ℝ) ≤ k.divisors.card := by
        exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
      have h2 : (k.divisors.card : ℝ) ≤ k := by exact_mod_cast Nat.card_divisors_le_self k
      rw [abs_of_nonneg (by linarith)]
      have : (k : ℝ) ≤ m := by exact_mod_cast hkm
      linarith
    exact mul_le_mul hω hcore (norm_nonneg _) (by positivity)
  have hsum : ‖∑ k ∈ Finset.Icc 2 m, (((k.divisors.card : ℝ) - 1 : ℝ) : ℂ) *
        ∑ i : Fin m → Letter d, aCoef L D m i *
          (if ∃ v : FreeGroup (Fin d), IsNonPower v ∧ wordFree (List.ofFn i) = v ^ k
           then (1 : ℂ) else 0)‖ ≤
      (m : ℝ) * ((m : ℝ) * (2 * (L.Dm : ℝ) ^ 12 * ((m : ℝ) + 1) ^ 12 * R ^ p)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hZ).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have : ((Finset.Icc 2 m).card : ℝ) ≤ m := by
      have : (Finset.Icc 2 m).card ≤ m := by simp
      exact_mod_cast this
    exact mul_le_mul_of_nonneg_right this (by positivity)
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  have hq1 : (1 : ℝ) ≤ L.q := by exact_mod_cast L.hq
  have hmq : (m : ℝ) ≤ L.q * ((p : ℝ) + 1) := by
    rw [hm]; push_cast; nlinarith
  have hm1q : (m : ℝ) + 1 ≤ L.q * ((p : ℝ) + 1) := by
    rw [hm]; push_cast; nlinarith
  have hp1 : (1 : ℝ) ≤ (p : ℝ) + 1 := by have : (0 : ℝ) ≤ p := Nat.cast_nonneg p; linarith
  have hRp : 0 ≤ R ^ p := by positivity
  have hDmn : 0 ≤ (L.Dm : ℝ) := Nat.cast_nonneg _
  have e1 : (m : ℝ) * ((m : ℝ) * (2 * (L.Dm : ℝ) ^ 12 * ((m : ℝ) + 1) ^ 12 * R ^ p)) ≤
      2 * (L.Dm : ℝ) ^ 12 * (L.q : ℝ) ^ 14 * ((p : ℝ) + 1) ^ 14 * R ^ p := by
    have h1 : (m : ℝ) * (m : ℝ) * ((m : ℝ) + 1) ^ 12 ≤ (L.q * ((p : ℝ) + 1)) ^ 14 := by
      calc (m : ℝ) * (m : ℝ) * ((m : ℝ) + 1) ^ 12
          ≤ (L.q * ((p : ℝ) + 1)) * (L.q * ((p : ℝ) + 1)) * (L.q * ((p : ℝ) + 1)) ^ 12 := by
            gcongr
        _ = (L.q * ((p : ℝ) + 1)) ^ 14 := by ring
    calc (m : ℝ) * ((m : ℝ) * (2 * (L.Dm : ℝ) ^ 12 * ((m : ℝ) + 1) ^ 12 * R ^ p))
        = (2 * (L.Dm : ℝ) ^ 12 * R ^ p) * ((m : ℝ) * (m : ℝ) * ((m : ℝ) + 1) ^ 12) := by ring
      _ ≤ (2 * (L.Dm : ℝ) ^ 12 * R ^ p) * (L.q * ((p : ℝ) + 1)) ^ 14 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have e2 : (L.Dm : ℝ) * R ^ p ≤ (L.Dm : ℝ) * ((p : ℝ) + 1) ^ 14 * R ^ p := by
    have : (1 : ℝ) ≤ ((p : ℝ) + 1) ^ 14 := one_le_pow₀ hp1
    nlinarith [mul_nonneg hDmn hRp]
  calc _ ≤ (L.Dm : ℝ) * R ^ p + 2 * (L.Dm : ℝ) ^ 12 * (L.q : ℝ) ^ 14 * ((p : ℝ) + 1) ^ 14 * R ^ p :=
        add_le_add hE (hsum.trans e1)
    _ ≤ _ := by nlinarith [e2, mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * (L.Dm : ℝ) ^ 12 * (L.q : ℝ) ^ 14) (by positivity : (0:ℝ) ≤ ((p : ℝ) + 1) ^ 14)) hRp]


/-! ## Corollary 9.7 -/

theorem asympCoeff_zero (m : ℕ) : asympCoeff (fun _ : ℕ => (0 : ℝ)) m = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [asympCoeff]
    have : ∀ i : Fin m, asympCoeff (fun _ : ℕ => (0 : ℝ)) i = 0 := fun i => ih i i.isLt
    simp only [this]
    simp
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).limUnder_eq

theorem supp_subset_Icc_of_extends_nu_one_dev {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (μ : smoothFun →ₗ[ℝ] ℝ) (hμ : IsCSDistribution μ)
    (hext : ∀ h : ℝ[X], μ (polyFun h) = nu P 1 h) :
    supp μ ⊆ Set.Icc (-‖P.eval (sLimit d)‖) ‖P.eval (sLimit d)‖ := by
  refine (supp_subset_Icc_limsup μ hμ).trans ?_
  set r := limsup (fun p : ℕ => |μ (polyFun (X ^ p))| ^ (1 / (p : ℝ))) atTop with hr
  have hρ0 : 0 ≤ ‖P.eval (sLimit d)‖ := norm_nonneg _
  have hle : r ≤ ‖P.eval (sLimit d)‖ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hmoment : ∀ p : ℕ, μ (polyFun (X ^ p)) = nu P 1 (X ^ p) := fun p => hext _
    simp only [hr, hmoment]
    by_cases hD : D = 0
    · -- no matrix coefficients: every moment vanishes
      subst hD
      have h0 : ∀ p : ℕ, nu P 1 (X ^ p) = 0 := by
        intro p
        have : (fun N : ℕ => expTr P N (fun x => (X ^ p : ℝ[X]).eval x)) = fun _ => 0 := by
          funext N; simp [expTr, uniformExp, trDN]
        simp only [nu, this]
        exact asympCoeff_zero 1
      simp only [h0, abs_zero]
      have : limsup (fun p : ℕ => (0 : ℝ) ^ (1 / (p : ℝ))) atTop ≤ ‖P.eval (sLimit d)‖ + ε := by
        apply limsup_le_of_le
        · exact isCoboundedUnder_le_of_le atTop (x := 0) fun p => Real.rpow_nonneg le_rfl _
        · filter_upwards [eventually_ge_atTop 1] with p hp
          have : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
          rw [Real.zero_rpow (by simpa using this)]
          positivity
      exact this
    · have hD1 : 1 ≤ D := Nat.pos_of_ne_zero hD
      obtain ⟨K0, s, hK0, hb⟩ := moment_bound P hP hD1 (ε / 2) (by positivity)
      have := limsup_pow_le (fun p => nu P 1 (X ^ p)) K0 s (‖P.eval (sLimit d)‖ + ε / 2)
        (by positivity) hK0 hb
      linarith
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩


end StrongConv.S9

end
end
end

section
open Polynomial
open StrongConv

theorem solution {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (μ : smoothFun →ₗ[ℝ] ℝ) (hμ : IsCSDistribution μ)
    (hext : ∀ h : ℝ[X], μ (polyFun h) = nu P 1 h) :
    supp μ ⊆ Set.Icc (-‖P.eval (sLimit d)‖) ‖P.eval (sLimit d)‖ := by
  apply StrongConv.S9.supp_subset_Icc_of_extends_nu_one_dev <;> assumption

end
