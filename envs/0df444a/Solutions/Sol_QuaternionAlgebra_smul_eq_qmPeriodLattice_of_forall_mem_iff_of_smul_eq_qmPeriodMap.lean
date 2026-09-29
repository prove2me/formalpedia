-- Prove2me | solution 1 for QuaternionAlgebra.smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/675fbb49-4ee8-56e3-85f7-9509d076a66e

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped Quaternion MatrixGroups Pointwise BigOperators
open QuaternionAlgebra

noncomputable section

namespace LevConst

theorem qmPeriodMap_injective {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : UpperHalfPlane) : Function.Injective (qmPeriodMap ι τ) := by
  intro x y hxy
  have h : qmPeriodMap ι τ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hτ : τ.im ≠ 0 := τ.im_pos.ne'
  have hτ' : (τ : ℂ).im ≠ 0 := τ.im_pos.ne'
  have hM : ι (x - y) = 0 := by
    ext i j
    have hi := congr_fun h i
    simp only [qmPeriodMap_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, mul_one, Complex.coe_algebraMap] at hi
    have h0 : ι (x - y) i 0 = 0 := by
      have := congrArg Complex.im hi
      simpa [hτ, hτ'] using this
    fin_cases j
    · exact h0
    · have := congrArg Complex.re hi
      simpa [h0] using this
  have : x - y = 0 := hι (by rw [hM, map_zero])
  exact sub_eq_zero.mp this

theorem qmPeriodMap_rat_smul {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane)
    (q : ℚ) (x : ℍ[ℚ, a, b]) : qmPeriodMap ι τ (q • x) = (q : ℂ) • qmPeriodMap ι τ x := by
  ext i
  simp only [qmPeriodMap_apply, map_smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
    Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Rat.smul_def, Complex.coe_algebraMap,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

theorem qmPeriodMap_sum_zsmul {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane)
    (m : Fin 4 → ℤ) (y : Fin 4 → ℍ[ℚ, a, b]) :
    qmPeriodMap ι τ (∑ i, (m i) • y i) = ∑ i, ((m i : ℤ) : ℂ) • qmPeriodMap ι τ (y i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

end LevConst

open LevConst in
theorem solution
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (J' : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) [NeZero N]
    (D : Set ℂ) (z₀ : ℂ) (hz₀ : z₀ ∈ D)
    (L ME : ℂ → Submodule ℤ (Fin 2 → ℂ)) (κ c : ℂ → ℂ) (v : Fin 4 → ℂ → (Fin 2 → ℂ))
    (y : Fin 4 → ℍ[ℚ, a, b]) (τ : ℂ → UpperHalfPlane) (T : Set (Fin 4 → ℤ))
    (hκ : ∀ z ∈ D, κ z ≠ 0) (hc : ∀ z ∈ D, c z ≠ 0)
    (hbasis : ∀ z ∈ D,
      (∀ i : Fin 4, v i z ∈ κ z • L z) ∧ ∀ x ∈ κ z • L z, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = x)
    (hME : ∀ z ∈ D, ∀ w : Fin 2 → ℂ,
      w ∈ ME z ↔ ∃ n ∈ T, (w : (Fin 2 → ℂ) ⧸ (L z).toAddSubgroup) =
        (((κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (L z).toAddSubgroup))
    (hper : ∀ z ∈ D, ∀ i : Fin 4, c z • v i z = qmPeriodMap ι (τ z) (y i))
    (h₀ : (c z₀ * κ z₀) • ME z₀ = qmPeriodLattice ι J' (τ z₀)) :
    ∀ z ∈ D, (c z * κ z) • ME z = qmPeriodLattice ι J' (τ z) := by
  classical
  intro z hz
  have hinj := LevConst.qmPeriodMap_injective ι hι
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)

  have hκL : ∀ z ∈ D, ∀ x : Fin 2 → ℂ, x ∈ κ z • L z ↔ ∃ m : Fin 4 → ℤ, (∑ i, ((m i : ℤ) : ℂ) • v i z) = x := by
    intro z hz x
    constructor
    · intro hx
      obtain ⟨m, hm, -⟩ := (hbasis z hz).2 x hx
      exact ⟨m, hm⟩
    · rintro ⟨m, rfl⟩
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ ((hbasis z hz).1 i)

  have hperX : ∀ z ∈ D, ∀ (n m : Fin 4 → ℤ),
      qmPeriodMap ι (τ z) (((N : ℚ)⁻¹) • (∑ i, (n i) • y i) + ∑ i, (m i) • y i) =
        c z • (((N : ℂ)⁻¹) • ∑ i, ((n i : ℤ) : ℂ) • v i z) + c z • ∑ i, ((m i : ℤ) : ℂ) • v i z := by
    intro z hz n m
    rw [map_add, LevConst.qmPeriodMap_rat_smul, LevConst.qmPeriodMap_sum_zsmul, LevConst.qmPeriodMap_sum_zsmul]
    simp_rw [← hper z hz]
    simp only [Finset.smul_sum, smul_smul]
    push_cast
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      ring

  set X₀ : Set ℍ[ℚ, a, b] := {x | ∃ n ∈ T, ∃ m : Fin 4 → ℤ,
      x = ((N : ℚ)⁻¹) • (∑ i, (n i) • y i) + ∑ i, (m i) • y i} with hX₀
  have hS : ∀ z ∈ D, (((c z * κ z) • ME z : Submodule ℤ (Fin 2 → ℂ)) : Set (Fin 2 → ℂ)) =
      qmPeriodMap ι (τ z) '' X₀ := by
    intro z hz
    have hκz := hκ z hz
    have hcz := hc z hz
    ext w'
    simp only [SetLike.mem_coe, Set.mem_image]
    constructor
    · intro hw'
      obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hw'
      obtain ⟨n, hnT, hq⟩ := (hME z hz w).mp hw
      have hℓ : -w + (κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, ((n i : ℤ) : ℂ) • v i z) ∈ L z := QuotientAddGroup.eq.mp hq
      have hκℓ : κ z • (w - (κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, ((n i : ℤ) : ℂ) • v i z)) ∈ κ z • L z := by
        refine Submodule.smul_mem_pointwise_smul _ _ _ ?_
        have := (L z).neg_mem hℓ
        rwa [neg_add, neg_neg, ← sub_eq_add_neg] at this
      obtain ⟨m, hm⟩ := (hκL z hz _).mp hκℓ
      refine ⟨_, ⟨n, hnT, m, rfl⟩, ?_⟩
      rw [hperX z hz n m, hm]
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      try ring
    · rintro ⟨x, ⟨n, hnT, m, rfl⟩, rfl⟩
      rw [hperX z hz n m]
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨(κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, ((n i : ℤ) : ℂ) • v i z) + (κ z)⁻¹ • ∑ i, ((m i : ℤ) : ℂ) • v i z, ?_, ?_⟩
      · refine (hME z hz _).mpr ⟨n, hnT, ?_⟩
        refine QuotientAddGroup.eq.mpr ?_
        obtain ⟨ℓ, hℓ, hℓeq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ((hκL z hz _).mpr ⟨m, rfl⟩)
        have hℓ' : (κ z)⁻¹ • ∑ i, ((m i : ℤ) : ℂ) • v i z = ℓ := by
          rw [← hℓeq, smul_smul, inv_mul_cancel₀ hκz, one_smul]
        have e : -((κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, ((n i : ℤ) : ℂ) • v i z) + (κ z)⁻¹ • ∑ i, ((m i : ℤ) : ℂ) • v i z) +
            (κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, ((n i : ℤ) : ℂ) • v i z) = -((κ z)⁻¹ • ∑ i, ((m i : ℤ) : ℂ) • v i z) := by
          abel
        rw [e, hℓ']
        exact (L z).neg_mem hℓ
      · ext j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        try ring

  have h0' : qmPeriodMap ι (τ z₀) '' X₀ = qmPeriodMap ι (τ z₀) '' (J' : Set ℍ[ℚ, a, b]) := by
    rw [← hS z₀ hz₀, h₀, qmPeriodLattice, Submodule.map_coe]
  have hX : X₀ = (J' : Set ℍ[ℚ, a, b]) := (hinj (τ z₀)).image_injective h0'
  refine SetLike.coe_injective ?_
  rw [hS z hz, hX, qmPeriodLattice, Submodule.map_coe]

end
end S_QuaternionAlgebra_smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap
end P2MW
export P2MW.S_QuaternionAlgebra_smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap (solution)
