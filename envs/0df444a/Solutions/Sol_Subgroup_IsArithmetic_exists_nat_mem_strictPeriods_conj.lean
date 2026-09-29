-- Prove2me | solution 1 for Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/dac764ca-64e0-5825-b105-2678ecee9162

import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj

open Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups Pointwise

noncomputable section

theorem solution (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] : ∃ M : ℕ, 0 < M ∧ ∀ γ : SL(2, ℤ), (M : ℝ) ∈ (ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ) • 𝒢).strictPeriods := by
  haveI : (𝒢.comap (mapGL (R := ℤ) ℝ)).FiniteIndex := Subgroup.IsArithmetic.finiteIndex_comap 𝒢
  set Λ : Subgroup SL(2, ℤ) := (𝒢.comap (mapGL (R := ℤ) ℝ)).normalCore with hΛ
  haveI : Λ.FiniteIndex := inferInstance
  haveI hN : Λ.Normal := inferInstance
  refine ⟨Λ.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun γ ↦ ?_⟩
  have hT : ModularGroup.T ^ Λ.index ∈ Λ := Λ.pow_index_mem ModularGroup.T
  have hconj : γ⁻¹ * ModularGroup.T ^ Λ.index * γ ∈ 𝒢.comap (mapGL ℝ) := by
    apply Subgroup.normalCore_le
    simpa using hN.conj_mem _ hT γ⁻¹
  have hU : ∀ m : ℤ, Matrix.GeneralLinearGroup.upperRightHom ((m : ℝ)) =
      mapGL ℝ (ModularGroup.T ^ m) := by
    intro m
    simp only [Units.ext_iff, mapGL_coe_matrix, map_apply_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow]
  have hU' := hU Λ.index
  rw [zpow_natCast, Int.cast_natCast] at hU'
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← toConjAct_inv,
    toConjAct_smul, inv_inv, hU', ← map_inv, ← map_mul, ← map_mul]
  exact hconj
end

end S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj
end P2MW
export P2MW.S_Subgroup_IsArithmetic_exists_nat_mem_strictPeriods_conj (solution)
