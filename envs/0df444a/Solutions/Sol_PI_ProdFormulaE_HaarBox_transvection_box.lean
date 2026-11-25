-- Prove2me | solution 1 for PI.ProdFormulaE.HaarBox.transvection_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:16.965681+00:00
-- url     : https://prove2.me/submissions/f38ec405-7757-42b3-9168-683e74612689

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarTransv
import Theorems.Thm_P2M_PI_ProdFormulaE_HaarBox_t__inv_0d2f4bd11c98
import Theorems.Thm_PI_ProdFormulaE_HaarBox_toLin_mem_box
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open ValuativeRel Module Matrix
namespace PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private theorem tGamma_apply_of_ne (t : Matrix.TransvectionStruct ι K) {k : ι}
    (hk : k ≠ t.i) : tγ t k = 1 := by
  simp [tγ, hk]
private theorem tGamma_apply_self (t : Matrix.TransvectionStruct ι K) :
    tγ t t.i = max (valuation K t.c) 1 := by
  simp [tγ]
end PI.ProdFormulaE.HaarBox
end
end

set_option autoImplicit false
noncomputable section
open ValuativeRel Module Matrix
open PI PI.ProdFormulaE PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.ProdFormulaE.HaarBox
theorem _root_.solution (b : Basis ι K E) (t : Matrix.TransvectionStruct ι K) :
    ∃ γ : ι → ValueGroupWithZero K, (∀ i, γ i ≠ 0) ∧
      Matrix.toLin b b t.toMatrix '' box b γ = box b γ := by
  refine ⟨tγ t, ?_, ?_⟩
  · intro i
    have h1 : (1 : ValueGroupWithZero K) ≤ tγ t i := by
      by_cases hi : i = t.i
      · rw [hi, tGamma_apply_self]
        exact le_max_right _ _
      · rw [tGamma_apply_of_ne t hi]
    exact (lt_of_lt_of_le zero_lt_one h1).ne'
  · apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact toLin_mem_box b t x hx
    · intro y hy
      refine ⟨Matrix.toLin b b t.inv.toMatrix y, ?_, ?_⟩
      · have h := toLin_mem_box b t.inv y (by rwa [tγ_inv])
        rwa [tγ_inv] at h
      · show ((Matrix.toLin b b t.toMatrix).comp (Matrix.toLin b b t.inv.toMatrix)) y = y
        rw [← Matrix.toLin_mul, Matrix.TransvectionStruct.mul_inv, Matrix.toLin_one,
          LinearMap.id_apply]
end PI.ProdFormulaE.HaarBox
