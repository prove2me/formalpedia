-- Prove2me | solution 1 for StrongConv.nuAdj_one_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:01:37.787473+00:00
-- url     : https://prove2.me/submissions/d3a37d2b-ef42-4845-a570-1401581784eb

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_tendsto_mul_uniformExp_trN_wordEval
import Theorems.Thm_StrongConv_tendsto_uniformExp_trN_wordEval


namespace StrongConv.L82
open FreeMonoid

lemma len_pow {β : Type*} (x : FreeMonoid β) (k : ℕ) : (x ^ k).length = k * x.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, length_mul, ih]; ring

lemma eq_of_pow_eq_len {β : Type*} {a b : FreeMonoid β} {l : ℕ} (hl : 0 < l) (h : a ^ l = b ^ l)
    (hlen : a.length = b.length) : a = b := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  rw [pow_succ', pow_succ'] at h
  have := congrArg FreeMonoid.toList h
  simp only [FreeMonoid.toList_mul] at this
  exact FreeMonoid.toList.injective (List.append_inj this hlen).1

lemma mul_pow_succ'' {β : Type*} (a b : FreeMonoid β) (n : ℕ) :
    (a * b) ^ (n + 1) = a * (b * a) ^ n * b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ih, pow_succ' (b * a) n]; simp only [mul_assoc]

lemma exists_prefix {β : Type*} {x y s t : FreeMonoid β} (h : x * s = y * t)
    (hlen : x.length ≤ y.length) : ∃ y', y = x * y' := by
  have h1 : x.toList <+: (x * s).toList := ⟨s.toList, rfl⟩
  have h2 : y.toList <+: (x * s).toList := by rw [h]; exact ⟨t.toList, rfl⟩
  obtain ⟨u, hu⟩ := List.prefix_of_prefix_length_le h1 h2 hlen
  exact ⟨FreeMonoid.ofList u, FreeMonoid.toList.injective (by simpa using hu.symm)⟩

lemma root_step {β : Type*} (x y : FreeMonoid β)
    (IH : ∀ x' y' : FreeMonoid β, x'.length + y'.length < x.length + y.length → x' ≠ 1 → y' ≠ 1 →
      ∀ k l : ℕ, 0 < k → 0 < l → x' ^ k = y' ^ l → ∃ r a b, x' = r ^ a ∧ y' = r ^ b)
    (hxy : x.length ≤ y.length) (hx : x ≠ 1) (hy : y ≠ 1) (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (h : x ^ k = y ^ l) : ∃ r a b, x = r ^ a ∧ y = r ^ b := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  have h' := h
  rw [pow_succ', pow_succ'] at h'
  obtain ⟨y', rfl⟩ := exists_prefix h' hxy
  by_cases hy' : y' = 1
  · subst hy'
    exact ⟨x, 1, 1, by simp, by simp⟩
  have hxl : 0 < x.length := Nat.pos_of_ne_zero (fun h0 => hx (length_eq_zero.mp h0))
  have hyl : 0 < y'.length := Nat.pos_of_ne_zero (fun h0 => hy' (length_eq_zero.mp h0))
  rw [mul_pow_succ'' x y' l'] at h
  have h1 : x ^ k' = (y' * x) ^ l' * y' := by
    have : x * x ^ k' = x * ((y' * x) ^ l' * y') := by
      rw [← pow_succ', h]; simp only [mul_assoc]
    exact mul_left_cancel this
  have h2 : (x * y') ^ (l' + 1) = (y' * x) ^ (l' + 1) := by
    rw [mul_pow_succ'' x y' l', ← h, pow_succ x k', h1, pow_succ]; simp only [mul_assoc]
  have h3 : x * y' = y' * x :=
    eq_of_pow_eq_len (Nat.succ_pos _) h2 (by rw [length_mul, length_mul, add_comm])
  have hc : Commute x y' := h3
  have h4 : x ^ k' = x ^ l' * y' ^ (l' + 1) := by
    rw [h1, (hc.symm).mul_pow, mul_assoc, pow_succ y' l']
    have e : x ^ l' * y' ^ l' = y' ^ l' * x ^ l' := (hc.pow_pow l' l').eq
    rw [← mul_assoc, ← e, mul_assoc]
  have hlen := congrArg FreeMonoid.length h4
  rw [len_pow, length_mul, len_pow, len_pow] at hlen
  have hkl : l' < k' := by
    by_contra hnot
    have hnot := not_lt.mp hnot
    have : k' * x.length ≤ l' * x.length := Nat.mul_le_mul_right _ hnot
    have : 0 < (l' + 1) * y'.length := Nat.mul_pos (Nat.succ_pos _) hyl
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hkl
  have h5 : x ^ (m + 1) = y' ^ (l' + 1) := by
    have : x ^ l' * x ^ (m + 1) = x ^ l' * y' ^ (l' + 1) := by
      rw [← pow_add, ← h4]; rfl
    exact mul_left_cancel this
  obtain ⟨r, a, b, ha, hb⟩ := IH y' x (by rw [length_mul]; omega) hy' hx (l' + 1) (m + 1)
    (Nat.succ_pos _) (Nat.succ_pos _) h5.symm
  exact ⟨r, b, b + a, hb, by rw [pow_add, ← hb, ← ha]⟩

lemma root_aux {β : Type*} : ∀ n : ℕ, ∀ x y : FreeMonoid β, x.length + y.length ≤ n → x ≠ 1 → y ≠ 1 →
    ∀ k l : ℕ, 0 < k → 0 < l → x ^ k = y ^ l → ∃ r a b, x = r ^ a ∧ y = r ^ b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro x y hn hx hy k l hk hl h
    have IH : ∀ x' y' : FreeMonoid β, x'.length + y'.length < x.length + y.length → x' ≠ 1 → y' ≠ 1 →
        ∀ k l : ℕ, 0 < k → 0 < l → x' ^ k = y' ^ l → ∃ r a b, x' = r ^ a ∧ y' = r ^ b :=
      fun x' y' hlt => ihn _ (by omega) x' y' le_rfl
    rcases le_total x.length y.length with hxy | hxy
    · exact root_step x y IH hxy hx hy k l hk hl h
    · obtain ⟨r, a, b, h1, h2⟩ := root_step y x
        (fun x' y' hlt => IH x' y' (by omega)) hxy hy hx l k hl hk h.symm
      exact ⟨r, b, a, h2, h1⟩

theorem root_pow {β : Type*} (x y : FreeMonoid β) (hx : x ≠ 1) (hy : y ≠ 1) (k l : ℕ) (hk : 0 < k)
    (hl : 0 < l) (h : x ^ k = y ^ l) : ∃ r a b, x = r ^ a ∧ y = r ^ b :=
  root_aux _ x y le_rfl hx hy k l hk hl h


section FG
open FreeGroup
variable {α : Type*} [DecidableEq α]

lemma aux_nil (e M M' : List (α × Bool)) (hM : IsCyclicallyReduced M) (hne' : M' ≠ [])
    (h : M = e ++ M' ++ invRev e) : e = [] := by
  rcases e with _ | ⟨a, e'⟩
  · rfl
  exfalso
  have h1 : M = a :: (e' ++ M' ++ invRev e') ++ [(a.1, !a.2)] := by
    rw [h, invRev_cons]; simp [invRev]
  rw [h1, isCyclicallyReduced_cons_append_iff] at hM
  have := hM.2 rfl
  simp at this

lemma cancel_core_le (c c' M M' : List (α × Bool)) (hM : IsCyclicallyReduced M)
    (hne' : M' ≠ []) (hle : c.length ≤ c'.length)
    (h : c ++ M ++ invRev c = c' ++ M' ++ invRev c') : c = c' ∧ M = M' := by
  have h1 : c <+: c ++ M ++ invRev c := ⟨M ++ invRev c, by simp⟩
  have h2 : c' <+: c ++ M ++ invRev c := by rw [h]; exact ⟨M' ++ invRev c', by simp⟩
  obtain ⟨e, rfl⟩ := List.prefix_of_prefix_length_le h1 h2 hle
  rw [invRev_append] at h
  have h3 : M ++ invRev c = (e ++ M' ++ invRev e) ++ invRev c := by
    have : c ++ (M ++ invRev c) = c ++ ((e ++ M' ++ invRev e) ++ invRev c) := by
      simpa [List.append_assoc] using h
    exact List.append_cancel_left this
  have h4 := List.append_cancel_right h3
  have he := aux_nil e M M' hM hne' h4
  subst he
  simpa using h4

lemma cancel_core (c c' M M' : List (α × Bool)) (hM : IsCyclicallyReduced M) (hM' : IsCyclicallyReduced M')
    (hne : M ≠ []) (hne' : M' ≠ [])
    (h : c ++ M ++ invRev c = c' ++ M' ++ invRev c') : c = c' ∧ M = M' := by
  rcases le_total c.length c'.length with hle | hle
  · exact cancel_core_le c c' M M' hM hne' hle h
  · obtain ⟨h1, h2⟩ := cancel_core_le c' c M' M hM' hne hle h.symm
    exact ⟨h1.symm, h2.symm⟩

end FG


section Roots
open FreeGroup FreeGroup.reduceCyclically
variable {α : Type*} [DecidableEq α]

lemma mk_flat {α : Type*} (C : List (α × Bool)) (n : ℕ) :
    mk (List.replicate n C).flatten = (mk C) ^ n := by
  induction n with
  | zero => simp; rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ← mul_mk, ih, pow_succ']

lemma core_ne_nil (v : FreeGroup α) (hv : v ≠ 1) : reduceCyclically v.toWord ≠ [] := by
  intro h
  apply hv
  have := congr_arg FreeGroup.mk (conj_conjugator_reduceCyclically v.toWord)
  rw [mk_toWord, h, List.append_nil, ← mul_mk, ← inv_mk, mul_inv_cancel] at this
  exact this.symm

lemma toWord_pow_eq (v : FreeGroup α) (k : ℕ) (hk : 1 ≤ k) : (v ^ k).toWord = conjugator v.toWord ++
    (List.replicate k (reduceCyclically v.toWord)).flatten ++ invRev (conjugator v.toWord) := by
  rw [toWord_pow, reduce_flatten_replicate isReduced_toWord, if_neg (by omega)]

lemma toList_pow_flat {β : Type*} (x : FreeMonoid β) (k : ℕ) :
    (x ^ k).toList = (List.replicate k x.toList).flatten := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', FreeMonoid.toList_mul, ih, List.replicate_succ, List.flatten_cons]

lemma conj_flat (c R : List (α × Bool)) (a : ℕ) :
    mk (c ++ (List.replicate a R).flatten ++ invRev c) = (mk (c ++ R ++ invRev c)) ^ a := by
  rw [← mul_mk, ← mul_mk, ← mul_mk, ← mul_mk, mk_flat, inv_mk.symm, conj_pow]

theorem root_unique (v u : FreeGroup α) (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) (hv : v ≠ 1) (hu : u ≠ 1)
    (hvnp : ∀ (w : FreeGroup α) (a : ℕ), 2 ≤ a → v ≠ w ^ a)
    (hunp : ∀ (w : FreeGroup α) (a : ℕ), 2 ≤ a → u ≠ w ^ a)
    (h : v ^ k = u ^ l) : v = u ∧ k = l := by
  set c := conjugator v.toWord with hc
  set C := reduceCyclically v.toWord with hC
  set c' := conjugator u.toWord with hc'
  set C' := reduceCyclically u.toWord with hC'
  have hCne := core_ne_nil v hv
  have hC'ne := core_ne_nil u hu
  have hw := congrArg toWord h
  rw [toWord_pow_eq v k hk, toWord_pow_eq u l hl] at hw
  have hcyc : IsCyclicallyReduced C := isCyclicallyReduced isReduced_toWord
  have hcyc' : IsCyclicallyReduced C' := isCyclicallyReduced isReduced_toWord
  have hne : (List.replicate k C).flatten ≠ [] := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [List.replicate_succ, List.flatten_cons]
    exact fun h => hCne (List.append_eq_nil_iff.mp h).1
  have hne' : (List.replicate l C').flatten ≠ [] := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
    rw [List.replicate_succ, List.flatten_cons]
    exact fun h => hC'ne (List.append_eq_nil_iff.mp h).1
  obtain ⟨hcc, hCC⟩ := cancel_core _ _ _ _ (hcyc.flatten_replicate k) (hcyc'.flatten_replicate l)
    hne hne' hw
  set x : FreeMonoid (α × Bool) := FreeMonoid.ofList C with hx
  set y : FreeMonoid (α × Bool) := FreeMonoid.ofList C' with hy
  have hx1 : x ≠ 1 := fun h0 => hCne (by simpa [hx] using congrArg FreeMonoid.toList h0)
  have hy1 : y ≠ 1 := fun h0 => hC'ne (by simpa [hy] using congrArg FreeMonoid.toList h0)
  have hxy : x ^ k = y ^ l := FreeMonoid.toList.injective (by
    rw [toList_pow_flat, toList_pow_flat]; exact hCC)
  obtain ⟨r, a, b, ha, hb⟩ := root_pow x y hx1 hy1 k l hk hl hxy
  have hvC : v = mk (c ++ C ++ invRev c) := by
    rw [hc, hC, conj_conjugator_reduceCyclically, mk_toWord]
  have huC : u = mk (c' ++ C' ++ invRev c') := by
    rw [hc', hC', conj_conjugator_reduceCyclically, mk_toWord]
  have hCa : C = (List.replicate a r.toList).flatten := by
    have := congrArg FreeMonoid.toList ha
    rw [toList_pow_flat] at this; exact this
  have hCb : C' = (List.replicate b r.toList).flatten := by
    have := congrArg FreeMonoid.toList hb
    rw [toList_pow_flat] at this; exact this
  have hvw : v = (mk (c ++ r.toList ++ invRev c)) ^ a := by rw [hvC, hCa, conj_flat]
  have huw : u = (mk (c' ++ r.toList ++ invRev c')) ^ b := by rw [huC, hCb, conj_flat]
  have ha1 : a = 1 := by
    by_contra hne1
    have ha0 : a ≠ 0 := by rintro rfl; apply hCne; simpa using hCa
    exact hvnp _ a (by omega) hvw
  have hb1 : b = 1 := by
    by_contra hne1
    have hb0 : b ≠ 0 := by rintro rfl; apply hC'ne; simpa using hCb
    exact hunp _ b (by omega) huw
  subst ha1 hb1
  have hCC' : C = C' := by rw [hCa, hCb]
  have hcc' : c = c' := hcc
  have hvu : v = u := by rw [hvC, huC, hCC', hcc']
  refine ⟨hvu, ?_⟩
  have := congrArg FreeMonoid.length hxy
  rw [len_pow, len_pow] at this
  have hxl : 0 < x.length := Nat.pos_of_ne_zero (fun h0 => hx1 (FreeMonoid.length_eq_zero.mp h0))
  have hyx : y.length = x.length := by rw [hx, hy, hCC']
  rw [hyx] at this
  exact Nat.eq_of_mul_eq_mul_right hxl this

end Roots

end StrongConv.L82

section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5

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


end StrongConv.S5
end
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartRoot

open FreeGroup FreeGroup.reduceCyclically

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

end StrongConv.S5.PartRoot

end
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartPerm

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

end StrongConv.S5.PartPerm


open Polynomial Filter Topology

noncomputable section

namespace StrongConv.L82

open StrongConv

section Alg
variable {R ι : Type*} [Ring R] [Fintype ι]

lemma sum_pow_words (f : ι → R) (p : ℕ) :
    (∑ i, f i) ^ p = ∑ x : Fin p → ι, (List.ofFn fun j => f (x j)).prod := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum]
    symm
    rw [← (Fin.consEquiv (fun _ : Fin (p + 1) => ι)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun x _ => ?_))
    simp [Fin.consEquiv, List.ofFn_succ]

end Alg


section Op
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma adj_sum {d : ℕ} (u : Fin d → H →L[ℂ] H) :
    ∑ i, (u i + star (u i)) = ∑ l : Fin d ⊕ Fin d, letterOp u l := by
  rw [Fintype.sum_sum_type]; simp [letterOp, Finset.sum_add_distrib]

lemma wordEval_ofFn {d p : ℕ} (u : Fin d → H →L[ℂ] H) (x : Fin p → Fin d ⊕ Fin d) :
    wordEval u (List.ofFn fun j => some (x j)) = (List.ofFn fun j => letterOp u (x j)).prod := by
  simp [wordEval, List.map_ofFn, Function.comp_def]

lemma adj_pow {d : ℕ} (u : Fin d → H →L[ℂ] H) (p : ℕ) :
    (∑ i, (u i + star (u i))) ^ p =
      ∑ x : Fin p → Fin d ⊕ Fin d, wordEval u (List.ofFn fun j => some (x j)) := by
  rw [adj_sum, sum_pow_words]
  simp_rw [wordEval_ofFn]

lemma isSA_adj {d : ℕ} (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (∑ i, (u i + star (u i))) := by
  unfold IsSelfAdjoint
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [star_add, star_star, add_comm]

end Op

lemma fnCalc_pow {A : Type*} [CStarAlgebra A] (T : A) (hT : IsSelfAdjoint T) (p : ℕ) :
    fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) T = T ^ p := by
  unfold fnCalc
  rw [← cfc_pow_id (R := ℂ) T p]
  refine cfc_congr (fun z hz => ?_)
  have := hT.mem_spectrum_eq_re hz
  simp only [eval_pow, eval_X, Complex.ofReal_pow]
  rw [← this]


lemma trN_sum {N : ℕ} {ι : Type*} (s : Finset ι) (Y : ι → (OnesPerp N →L[ℂ] OnesPerp N)) :
    trN N (∑ x ∈ s, Y x) = ∑ x ∈ s, trN N (Y x) := by
  unfold trN
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum, Complex.re_sum, Finset.sum_div]

lemma uniformExp_sum {X : Type*} [Fintype X] {ι : Type*} (s : Finset ι) (f : ι → X → ℝ) :
    uniformExp (fun a => ∑ x ∈ s, f x a) = ∑ x ∈ s, uniformExp (f x) := by
  unfold uniformExp
  rw [Finset.sum_comm, Finset.sum_div]

/-- the word of letters `x` -/
def wd {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) : List (Letter d) := List.ofFn fun j => some (x j)

/-- the group element of the word -/
def gx {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) : FreeGroup (Fin d) := wordFree (wd x)

/-- `E tr_N` of the word -/
def aN {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) (N : ℕ) : ℝ :=
  uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) (wd x)))

lemma F_eq (d p N : ℕ) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      trN N (fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) (adjPerp σ))) =
      ∑ x : Fin p → Fin d ⊕ Fin d, aN x N := by
  have h : ∀ σ : Fin d → Equiv.Perm (Fin N),
      trN N (fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) (adjPerp σ)) =
        ∑ x : Fin p → Fin d ⊕ Fin d, trN N (wordEval (sModel σ) (wd x)) := by
    intro σ
    unfold adjPerp
    rw [fnCalc_pow _ (isSA_adj (sModel σ)) p, adj_pow, trN_sum]
    rfl
  simp_rw [h]
  rw [uniformExp_sum]
  rfl

lemma tau_adj_pow (d p : ℕ) :
    tau (adjFree d ^ p) = ∑ x : Fin p → Fin d ⊕ Fin d, tau (wordEval (sLimit d) (wd x)) := by
  have : adjFree d ^ p = ∑ x : Fin p → Fin d ⊕ Fin d, wordEval (sLimit d) (wd x) :=
    adj_pow (sLimit d) p
  rw [this]
  unfold tau
  simp [inner_sum]


section Count
open FreeGroup

theorem key {d : ℕ} (g : FreeGroup (Fin d)) (hg : g ≠ 1) :
    ∃ (v : FreeGroup (Fin d)) (k : ℕ), IsNonPower v ∧ 1 ≤ k ∧ g = v ^ k ∧
      k ≤ g.toWord.length ∧ ∀ (v' : FreeGroup (Fin d)) (k' : ℕ), IsNonPower v' → 1 ≤ k' →
        g = v' ^ k' → v' = v ∧ k' = k := by
  obtain ⟨v, k, hv, hk, hg'⟩ := S5.PartRoot.exists_nonpower_pow g hg
  refine ⟨v, k, hv, hk, hg', ?_, ?_⟩
  · have := S5.PartRoot.length_toWord_pow_ge v hv.1 k
    rwa [← hg'] at this
  · intro v' k' hv' hk' h
    exact root_unique v' v k' k hk' hk hv'.1 hv.1 hv'.2 hv.2 (h.symm.trans hg') |>.imp id id

lemma wordFree_map_some_eq {d : ℕ} (l : List (Fin d ⊕ Fin d)) :
    wordFree (l.map some) = FreeGroup.mk (l.map (Sum.elim (fun i => (i, true)) fun i => (i, false))) := by
  induction l with
  | nil => simp [wordFree]; rfl
  | cons a l ih =>
    have h1 : wordFree (some a :: l.map some) = (Sum.elim FreeGroup.of (fun i => (FreeGroup.of i)⁻¹) a) *
        wordFree (l.map some) := by
      cases a <;> simp [wordFree]
    rw [List.map_cons, h1, ih, List.map_cons, ← List.singleton_append, ← mul_mk]
    congr 1
    cases a with
    | inl i => rfl
    | inr i =>
      simp only [Sum.elim_inr]
      rw [of, inv_mk]
      simp [invRev]

lemma length_gx_le {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) : (gx x).toWord.length ≤ p := by
  unfold gx wd
  have : (List.ofFn fun j => some (x j)) = (List.ofFn x).map some := by
    rw [List.map_ofFn]; rfl
  rw [this, wordFree_map_some_eq]
  have h := FreeGroup.norm_mk_le (L₁ := (List.ofFn x).map (Sum.elim (fun i => (i, true)) fun i => (i, false)))
  simpa [FreeGroup.norm] using h

open Classical in
/-- The weighted indicator of the word. -/
def T (d p : ℕ) (x : Fin p → Fin d ⊕ Fin d) : ℝ :=
  ∑ k ∈ Finset.Icc 2 p, ((k.divisors.card : ℝ) - 1) *
    (if ∃ v, IsNonPower v ∧ gx x = v ^ k then 1 else 0)

lemma T_one {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) (hx : gx x = 1) : T d p x = 0 := by
  unfold T
  refine Finset.sum_eq_zero (fun k hk => ?_)
  have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.1 hk).1; omega
  rw [if_neg, mul_zero]
  rintro ⟨v, hv, h⟩
  rw [hx] at h
  have : v ^ k = 1 ^ k := by rw [← h, one_pow]
  have := pow_left_injective (by omega : k ≠ 0) this
  exact hv.1 (by simpa using this)

lemma T_ne {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) (hx : gx x ≠ 1) :
    ∃ (v : FreeGroup (Fin d)) (k : ℕ), IsNonPower v ∧ 1 ≤ k ∧ gx x = v ^ k ∧
      T d p x = (k.divisors.card : ℝ) - 1 := by
  obtain ⟨v, k, hv, hk, hg, hlen, huniq⟩ := key (gx x) hx
  refine ⟨v, k, hv, hk, hg, ?_⟩
  have hkp : k ≤ p := hlen.trans (length_gx_le x)
  unfold T
  have hiff : ∀ k' ∈ Finset.Icc 2 p, (∃ v, IsNonPower v ∧ gx x = v ^ k') ↔ k' = k := by
    intro k' hk'
    have hk'1 : 1 ≤ k' := by have := (Finset.mem_Icc.1 hk').1; omega
    constructor
    · rintro ⟨v', hv', h⟩
      exact (huniq v' k' hv' hk'1 h).2
    · rintro rfl; exact ⟨v, hv, hg⟩
  by_cases hkmem : k ∈ Finset.Icc 2 p
  · rw [Finset.sum_eq_single_of_mem k hkmem]
    · rw [if_pos ((hiff k hkmem).2 rfl), mul_one]
    · intro k' hk' hne
      rw [if_neg (fun h => hne ((hiff k' hk').1 h)), mul_zero]
  · have hk1 : k = 1 := by
      by_contra hne
      exact hkmem (Finset.mem_Icc.2 ⟨by omega, hkp⟩)
    subst hk1
    rw [Finset.sum_eq_zero]
    · simp
    · intro k' hk'
      rw [if_neg, mul_zero]
      intro h
      have := (hiff k' hk').1 h
      subst this
      exact hkmem hk'

open Classical in
lemma card_eq (d p k : ℕ) (hk : 1 ≤ k) :
    (Nat.card {z : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
        IsNonPower z.2 ∧ wordFree (List.ofFn fun j => some (z.1 j)) = z.2 ^ k} : ℝ) =
      ((Finset.univ.filter fun x : Fin p → Fin d ⊕ Fin d =>
        ∃ v, IsNonPower v ∧ gx x = v ^ k).card : ℝ) := by
  classical
  have e : Nat.card {z : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
        IsNonPower z.2 ∧ wordFree (List.ofFn fun j => some (z.1 j)) = z.2 ^ k} =
      Nat.card {x : Fin p → Fin d ⊕ Fin d // ∃ v, IsNonPower v ∧ gx x = v ^ k} := by
    refine Nat.card_congr (Equiv.ofBijective (fun z => ⟨z.1.1, z.1.2, z.2.1, z.2.2⟩) ⟨?_, ?_⟩)
    · rintro ⟨⟨x, v⟩, hv, h⟩ ⟨⟨x', v'⟩, hv', h'⟩ heq
      simp only [Subtype.mk.injEq] at heq
      obtain rfl := heq
      have : v ^ k = v' ^ k := by rw [← h, ← h']
      have := pow_left_injective (by omega : k ≠ 0) this
      subst this
      rfl
    · rintro ⟨x, v, hv, h⟩
      exact ⟨⟨⟨x, v⟩, hv, h⟩, rfl⟩
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma sum_card_eq (d p : ℕ) :
    ∑ k ∈ Finset.Icc 2 p, ((k.divisors.card : ℝ) - 1) *
      (Nat.card {z : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
        IsNonPower z.2 ∧ wordFree (List.ofFn fun j => some (z.1 j)) = z.2 ^ k} : ℝ) =
    ∑ x : Fin p → Fin d ⊕ Fin d, T d p x := by
  classical
  unfold T
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk1 : 1 ≤ k := by have := (Finset.mem_Icc.1 hk).1; omega
  rw [card_eq d p k hk1, Finset.natCast_card_filter, Finset.mul_sum]

end Count


section Limits

lemma aN_one {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) (hx : gx x = 1) {N : ℕ} (hN : 1 ≤ N) :
    aN x N = ((N : ℝ) - 1) / N := by
  have h : ∀ σ : Fin d → Equiv.Perm (Fin N), trN N (wordEval (sModel σ) (wd x)) = ((N : ℝ) - 1) / N := by
    intro σ
    rw [S5.PartPerm.trN_wordEval_sModel, S5.PartPerm.wordPerm_eq_lift]
    have : wordFree (wd x) = 1 := hx
    rw [this, map_one]
    simp [S5.fixCount]
  unfold aN
  simp_rw [h]
  unfold uniformExp
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin d → Equiv.Perm (Fin N)) := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp

lemma tendsto_aN {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) :
    Tendsto (aN x) atTop (𝓝 (if gx x = 1 then 1 else 0)) := by
  have h := tendsto_uniformExp_trN_wordEval d (wd x)
  have h2 := (Complex.continuous_re.tendsto _).comp h
  rw [S5.PartPerm.tau_wordEval_sLimit] at h2
  have e : (if wordFree (wd x) = 1 then (1 : ℂ) else 0).re = if gx x = 1 then 1 else 0 := by
    unfold gx; split_ifs <;> simp
  rw [Function.comp_def, e] at h2
  exact h2

lemma tendsto_word {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) :
    Tendsto (fun N : ℕ => (N : ℝ) * (aN x N - (if gx x = 1 then 1 else 0))) atTop
      (𝓝 ((if gx x = 1 then -1 else 0) + T d p x)) := by
  by_cases hx : gx x = 1
  · rw [if_pos hx, T_one x hx, add_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [if_pos hx, aN_one x hx hN]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
    ring
  · obtain ⟨v, k, hv, hk, hg, hT⟩ := T_ne x hx
    simp only [if_neg hx, hT, zero_add, sub_zero]
    have := tendsto_mul_uniformExp_trN_wordEval d (wd x) hx v k hv hk hg
    simpa [aN] using this

end Limits

theorem nuAdj_one_pow_eq_dev (d p : ℕ) (hp : 1 ≤ p) :
    nuAdj d 1 (X ^ p) = -(tau (adjFree d ^ p)).re +
      ∑ k ∈ Finset.Icc 2 p, ((k.divisors.card : ℝ) - 1) *
        Nat.card {x : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
          IsNonPower x.2 ∧ wordFree (List.ofFn fun j => some (x.1 j)) = x.2 ^ k} := by
  set F : ℕ → ℝ := fun N => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      trN N (fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) (adjPerp σ))) with hFdef
  have hF : ∀ N, F N = ∑ x : Fin p → Fin d ⊕ Fin d, aN x N := fun N => F_eq d p N
  set c0 : ℝ := ∑ x : Fin p → Fin d ⊕ Fin d, (if gx x = 1 then (1 : ℝ) else 0) with hc0def
  have hlim : Tendsto F atTop (𝓝 c0) := by
    have : F = fun N => ∑ x : Fin p → Fin d ⊕ Fin d, aN x N := funext hF
    rw [this]
    exact tendsto_finsetSum _ (fun x _ => tendsto_aN x)
  have hc0 : asympCoeff F 0 = c0 := by
    rw [asympCoeff]
    have : (fun N : ℕ => (N : ℝ) ^ 0 * (F N - ∑ i : Fin 0, asympCoeff F i / (N : ℝ) ^ (i : ℕ))) = F := by
      funext N; simp
    rw [this]
    exact hlim.limUnder_eq
  have hlim1 : Tendsto (fun N : ℕ => (N : ℝ) ^ 1 * (F N - c0)) atTop
      (𝓝 (∑ x : Fin p → Fin d ⊕ Fin d, ((if gx x = 1 then -1 else 0) + T d p x))) := by
    have : ∀ N : ℕ, (N : ℝ) ^ 1 * (F N - c0) =
        ∑ x : Fin p → Fin d ⊕ Fin d, (N : ℝ) * (aN x N - (if gx x = 1 then 1 else 0)) := by
      intro N
      rw [hF, hc0def, pow_one, ← Finset.sum_sub_distrib, Finset.mul_sum]
    simp_rw [this]
    exact tendsto_finsetSum _ (fun x _ => tendsto_word x)
  have h1 : asympCoeff F 1 = ∑ x : Fin p → Fin d ⊕ Fin d, ((if gx x = 1 then -1 else 0) + T d p x) := by
    rw [asympCoeff]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
      Fin.val_zero, pow_zero, div_one]
    rw [hc0]
    exact hlim1.limUnder_eq
  have h2 : (tau (adjFree d ^ p)).re = c0 := by
    rw [tau_adj_pow, Complex.re_sum, hc0def]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [S5.PartPerm.tau_wordEval_sLimit]
    unfold gx
    split_ifs <;> simp
  show asympCoeff F 1 = _
  rw [h1, h2, sum_card_eq, Finset.sum_add_distrib, hc0def, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs <;> simp

end StrongConv.L82

namespace StrongConv

theorem nuAdj_one_pow_eq_dev (d p : ℕ) (hp : 1 ≤ p) :
    nuAdj d 1 (X ^ p) = -(tau (adjFree d ^ p)).re +
      ∑ k ∈ Finset.Icc 2 p, ((k.divisors.card : ℝ) - 1) *
        Nat.card {x : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
          IsNonPower x.2 ∧ wordFree (List.ofFn fun j => some (x.1 j)) = x.2 ^ k} :=
  L82.nuAdj_one_pow_eq_dev d p hp

end StrongConv

end

theorem solution : type_of% @StrongConv.nuAdj_one_pow_eq_dev :=
  @StrongConv.nuAdj_one_pow_eq_dev
