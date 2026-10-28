-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P38.unitaryColumn_iff_cokernel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:02:54.89936+00:00
-- url     : https://prove2.me/submissions/daf5f9dc-3a08-4165-8d4b-8265a70ad2a6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38
noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P38

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ}

lemma S170H_inner_sl (j : Fin n) (a : H) (x : HilbertPower H n) :
    inner ℂ (PiLp.single 2 j a : HilbertPower H n) x = inner ℂ a (x j) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · rw [PiLp.single_eq_same]
  · intro i _ hi; rw [PiLp.single_eq_of_ne 2 hi, inner_zero_left]
  · simp

lemma S170H_inner_sr (j : Fin n) (a : H) (x : HilbertPower H n) :
    inner ℂ x (PiLp.single 2 j a : HilbertPower H n) = inner ℂ (x j) a := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · rw [PiLp.single_eq_same]
  · intro i _ hi; rw [PiLp.single_eq_of_ne 2 hi, inner_zero_right]
  · simp

lemma S170H_inner_ss (j j' : Fin n) (a b : H) :
    inner ℂ (PiLp.single 2 j a : HilbertPower H n) (PiLp.single 2 j' b) =
      if j = j' then inner ℂ a b else 0 := by
  rw [S170H_inner_sl]
  split_ifs with h
  · subst h; rw [PiLp.single_eq_same]
  · rw [PiLp.single_eq_of_ne 2 h, inner_zero_right]

/-- Continuous linear inclusion of a coordinate. -/
def S170H_sg (j : Fin n) : H →L[ℂ] HilbertPower H n :=
  (LinearMap.isometryOfInner
    { toFun := fun a : H => (PiLp.single 2 j a : HilbertPower H n)
      map_add' := fun a b => by rw [PiLp.single_add]
      map_smul' := fun c a => by
        ext i
        by_cases h : i = j
        · subst h; simp only [PiLp.single_eq_same, RingHom.id_apply, PiLp.smul_apply]
        · simp only [PiLp.single_eq_of_ne 2 h, RingHom.id_apply, PiLp.smul_apply, smul_zero] }
    (fun a b => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [S170H_inner_ss, if_pos rfl])).toContinuousLinearMap

@[simp] lemma S170H_sg_apply (j : Fin n) (a : H) : S170H_sg j a = PiLp.single 2 j a := rfl

lemma S170H_op_ext {A B : Operators H} (h : ∀ ξ η, inner ℂ ξ (A η) = inner ℂ ξ (B η)) : A = B :=
  ContinuousLinearMap.ext fun η => ext_inner_left ℂ fun ξ => h ξ η

lemma S170H_star_inner (A : Operators H) (ξ η : H) : inner ℂ ξ (star A η) = inner ℂ (A ξ) η := by
  rw [ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_adjoint]

/-- Matrix of an operator on the Hilbert power. -/
def S170H_mat (T : HilbertPower H n →L[ℂ] HilbertPower H n) : Matrix (Fin n) (Fin n) (Operators H) :=
  fun i j => (PiLp.proj 2 (fun _ : Fin n => H) i).comp (T.comp (S170H_sg j))

lemma S170H_mat_apply (T : HilbertPower H n →L[ℂ] HilbertPower H n) (i j : Fin n) (ξ : H) :
    S170H_mat T i j ξ = T (PiLp.single 2 j ξ) i := rfl

lemma S170H_unitary (T : HilbertPower H n ≃ₗᵢ[ℂ] HilbertPower H n) :
    IsUnitaryMatrix (S170H_mat T.toContinuousLinearEquiv.toContinuousLinearMap) := by
  set U := S170H_mat T.toContinuousLinearEquiv.toContinuousLinearMap with hU
  have hUa : ∀ i j ξ, U i j ξ = T (PiLp.single 2 j ξ) i := fun _ _ _ => rfl
  -- adjoint entries
  have hstar : ∀ i j ξ, star (U i j) ξ = T.symm (PiLp.single 2 i ξ) j := by
    intro i j ξ
    refine ext_inner_left ℂ fun ζ => ?_
    rw [S170H_star_inner, hUa, ← S170H_inner_sr, LinearIsometryEquiv.inner_map_eq_flip, S170H_inner_sl]
  constructor
  · refine Matrix.ext fun j j' => ?_
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine S170H_op_ext fun ξ η => ?_
    simp only [Matrix.star_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply, inner_sum]
    simp only [S170H_star_inner, hUa]
    rw [← PiLp.inner_apply, LinearIsometryEquiv.inner_map_map, S170H_inner_ss]
    split_ifs <;> simp
  · refine Matrix.ext fun i i' => ?_
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine S170H_op_ext fun ξ η => ?_
    simp only [Matrix.star_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply, inner_sum]
    have : ∀ j, inner ℂ ξ (U i j (star (U i' j) η)) = inner ℂ (star (U i j) ξ) (star (U i' j) η) := by
      intro j
      have := S170H_star_inner (star (U i j)) ξ (star (U i' j) η)
      rwa [star_star] at this
    simp only [this]
    simp only [hstar]
    rw [← PiLp.inner_apply, LinearIsometryEquiv.inner_map_map, S170H_inner_ss]
    split_ifs <;> simp

/-- The column map ξ ↦ (a i ξ)_i. -/
def S170H_V (a : Fin n → Operators H) : H →L[ℂ] HilbertPower H n := ∑ i, (S170H_sg i).comp (a i)

lemma S170H_V_apply (a : Fin n → Operators H) (ξ : H) (i : Fin n) : S170H_V a ξ i = a i ξ := by
  simp only [S170H_V, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, S170H_sg_apply,
    WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [PiLp.single_eq_same]
  · intro b _ hb; rw [PiLp.single_eq_of_ne 2 (Ne.symm hb)]
  · simp

lemma S170H_C_apply (a : Fin n → Operators H) (x : HilbertPower H n) :
    columnAdjoint H a x = ∑ i, star (a i) (x i) := by
  simp [columnAdjoint]

lemma S170H_VC (a : Fin n → Operators H) (ξ : H) (x : HilbertPower H n) :
    inner ℂ (S170H_V a ξ) x = inner ℂ ξ (columnAdjoint H a x) := by
  rw [PiLp.inner_apply, S170H_C_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S170H_V_apply, S170H_star_inner]

lemma S170H_CV (a : Fin n → Operators H) (ha : columnSquares a = 1) (ξ : H) :
    columnAdjoint H a (S170H_V a ξ) = ξ := by
  rw [S170H_C_apply]
  simp only [S170H_V_apply]
  have := congrArg (fun A : Operators H => A ξ) ha
  simpa [columnSquares, ContinuousLinearMap.sum_apply] using this

/-- Drop the first coordinate. -/
def S170H_tail (m : ℕ) : HilbertPower H (m + 1) →L[ℂ] HilbertPower H m :=
  ∑ k, (S170H_sg k).comp (PiLp.proj 2 (fun _ : Fin (m + 1) => H) k.succ)

lemma S170H_tail_apply (m : ℕ) (z : HilbertPower H (m + 1)) (k : Fin m) : S170H_tail m z k = z k.succ := by
  simp only [S170H_tail, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, S170H_sg_apply,
    WithLp.ofLp_sum, Finset.sum_apply, PiLp.proj_apply]
  rw [Finset.sum_eq_single k]
  · rw [PiLp.single_eq_same]
  · intro b _ hb; rw [PiLp.single_eq_of_ne 2 (Ne.symm hb)]
  · simp

lemma S170H_back {m : ℕ} (a : Fin (m + 1) → Operators H) (ha : columnSquares a = 1)
    (φ : ColumnCokernel H a ≃ₗᵢ[ℂ] HilbertPower H m) : IsUnitaryColumn a := by
  set K := ColumnCokernel H a
  let T : HilbertPower H (m + 1) →L[ℂ] HilbertPower H (m + 1) :=
    (S170H_V a).comp (PiLp.proj 2 (fun _ : Fin (m + 1) => H) 0) +
      K.subtypeL.comp (φ.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (S170H_tail m))
  have hT : ∀ z, T z = S170H_V a (z 0) + (φ.symm (S170H_tail m z) : HilbertPower H (m + 1)) := fun z => rfl
  have hK : ∀ y : K, columnAdjoint H a (y : HilbertPower H (m + 1)) = 0 := fun y => y.2
  have hiso : ∀ z w, inner ℂ (T z) (T w) = inner ℂ z w := by
    intro z w
    rw [hT, hT, inner_add_left, inner_add_right, inner_add_right, S170H_VC, S170H_VC, S170H_CV a ha, hK,
      inner_zero_right, add_zero, ← inner_conj_symm (φ.symm (S170H_tail m z) : HilbertPower H (m + 1)), S170H_VC,
      hK, inner_zero_right, map_zero, zero_add, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map,
      PiLp.inner_apply, PiLp.inner_apply z w, Fin.sum_univ_succ]
    simp only [S170H_tail_apply]
  have hsurj : Function.Surjective T := by
    intro x
    have hmem : x - S170H_V a (columnAdjoint H a x) ∈ K := by
      show columnAdjoint H a (x - S170H_V a (columnAdjoint H a x)) = 0
      rw [map_sub, S170H_CV a ha, sub_self]
    set y := φ ⟨_, hmem⟩
    refine ⟨WithLp.toLp 2 (Fin.cons (columnAdjoint H a x) (fun k => y k)), ?_⟩
    have htail : S170H_tail m (WithLp.toLp 2 (Fin.cons (columnAdjoint H a x) (fun k => y k) : Fin (m + 1) → H)) = y := by
      ext k; rw [S170H_tail_apply]; simp
    rw [hT, htail]
    simp [y]
  let Ti : HilbertPower H (m + 1) →ₗᵢ[ℂ] HilbertPower H (m + 1) := LinearMap.isometryOfInner T.toLinearMap hiso
  let Te := LinearIsometryEquiv.ofSurjective Ti hsurj
  refine ⟨S170H_mat Te.toContinuousLinearEquiv.toContinuousLinearMap, S170H_unitary Te, 0, fun i => ?_⟩
  ext ξ
  rw [S170H_mat_apply]
  show T (PiLp.single 2 0 ξ) i = a i ξ
  have h0 : S170H_tail m (PiLp.single 2 (0 : Fin (m + 1)) ξ) = 0 := by
    ext k; rw [S170H_tail_apply, PiLp.single_eq_of_ne 2 (Fin.succ_ne_zero k)]; rfl
  rw [hT, h0, map_zero, PiLp.single_eq_same]
  simp [S170H_V_apply]

lemma S170H_fwd {m : ℕ} (a : Fin (m + 1) → Operators H) (hu : IsUnitaryColumn a) :
    Nonempty (ColumnCokernel H a ≃ₗᵢ[ℂ] HilbertPower H m) := by
  obtain ⟨U, ⟨h1, h2⟩, j, hj⟩ := hu
  set K := ColumnCokernel H a
  have hE1 : ∀ p q, ∑ i, star (U i p) * U i q = if p = q then 1 else 0 := by
    intro p q
    have := congrFun (congrFun h1 p) q
    rwa [Matrix.mul_apply, Matrix.one_apply] at this
  have hE2 : ∀ i i', ∑ p, U i p * star (U i' p) = if i = i' then 1 else 0 := by
    intro i i'
    have := congrFun (congrFun h2 i) i'
    rwa [Matrix.mul_apply, Matrix.one_apply] at this
  have hpair : ∀ p q (ξ η : H), ∑ i, inner ℂ (U i p ξ) (U i q η) = if p = q then inner ℂ ξ η else 0 := by
    intro p q ξ η
    have e : ∀ i, inner ℂ (U i p ξ) (U i q η) = inner ℂ ξ ((star (U i p) * U i q) η) := fun i => by
      rw [ContinuousLinearMap.mul_apply, S170H_star_inner]
    simp only [e]
    rw [← inner_sum, ← ContinuousLinearMap.sum_apply, hE1]
    split_ifs <;> simp
  let Φ : HilbertPower H m →L[ℂ] HilbertPower H (m + 1) :=
    ∑ k, (S170H_V (fun i => U i (j.succAbove k))).comp (PiLp.proj 2 (fun _ : Fin m => H) k)
  have hΦ : ∀ y i, Φ y i = ∑ k, U i (j.succAbove k) (y k) := by
    intro y i
    simp only [Φ, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, WithLp.ofLp_sum,
      Finset.sum_apply, S170H_V_apply, PiLp.proj_apply]
  have hiso : ∀ y y', inner ℂ (Φ y) (Φ y') = inner ℂ y y' := by
    intro y y'
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp only [hΦ, sum_inner, inner_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    simp only [hpair, (Fin.succAbove_right_injective (p := j)).eq_iff]
    rw [Finset.sum_ite_eq']
    simp
  have hC : ∀ x : HilbertPower H (m + 1), columnAdjoint H a x = ∑ i, star (U i j) (x i) := by
    intro x; rw [S170H_C_apply]; simp only [hj]
  have hrange : ∀ y, Φ y ∈ K := by
    intro y
    show columnAdjoint H a (Φ y) = 0
    rw [hC]
    simp only [hΦ, map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    have e : ∀ x, star (U x j) (U x (j.succAbove k) (y k)) = (star (U x j) * U x (j.succAbove k)) (y k) :=
      fun x => rfl
    simp only [e]
    rw [← ContinuousLinearMap.sum_apply, hE1, if_neg (Fin.succAbove_ne j k).symm]
    rfl
  have hsurj : ∀ x ∈ K, ∃ y, Φ y = x := by
    intro x hx
    have hx0 : ∑ i, star (U i j) (x i) = 0 := by rw [← hC]; exact hx
    refine ⟨WithLp.toLp 2 (fun k => ∑ i, star (U i (j.succAbove k)) (x i)), ?_⟩
    ext i'
    rw [hΦ]
    simp only [map_sum]
    have hfull : ∑ p, ∑ i, U i' p (star (U i p) (x i)) = x i' := by
      rw [Finset.sum_comm]
      have e : ∀ i, ∑ p, U i' p (star (U i p) (x i)) = (∑ p, U i' p * star (U i p)) (x i) := fun i => by
        rw [ContinuousLinearMap.sum_apply]; rfl
      simp only [e, hE2]
      rw [Finset.sum_eq_single i']
      · simp
      · intro b _ hb; rw [if_neg (Ne.symm hb)]; rfl
      · simp
    rw [← hfull, Fin.sum_univ_succAbove _ j]
    have hj0 : ∑ i, U i' j (star (U i j) (x i)) = 0 := by rw [← map_sum, hx0, map_zero]
    rw [hj0, zero_add]
  let Ψ : HilbertPower H m →ₗ[ℂ] K := LinearMap.codRestrict K Φ.toLinearMap hrange
  have hΨ : ∀ y y', inner ℂ (Ψ y) (Ψ y') = inner ℂ y y' := fun y y' => by
    rw [Submodule.coe_inner]; exact hiso y y'
  let Ψi := LinearMap.isometryOfInner Ψ hΨ
  have hΨs : Function.Surjective Ψi := by
    intro x
    obtain ⟨y, hy⟩ := hsurj x x.2
    exact ⟨y, Subtype.ext hy⟩
  exact ⟨(LinearIsometryEquiv.ofSurjective Ψi hΨs).symm⟩

end QAlgorithms.Papers.Independent.Renew46.P38

open QAlgorithms.Papers.Independent.Renew46.P38

universe u

theorem solution (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → Operators H) (ha : columnSquares a = 1) :
    IsUnitaryColumn a ↔
      Nonempty ((ColumnCokernel H a) ≃ₗᵢ[ℂ] HilbertPower H (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact ⟨S170H_fwd a, fun ⟨φ⟩ => S170H_back a ha φ⟩
