-- Prove2me | solution 1 for PI.CntNotIntW.tensorLiftSurjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:58.933984+00:00
-- url     : https://prove2.me/submissions/696013d1-965c-49b2-b444-231ade75a48a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_DSurjDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_T2SpaceOfNonarchimedeanLocalField
import Theorems.Thm_P2M_PI_CntNotIntW_t2Space_of_nonarchimedeanLocalField__ad798eed03bb
import Theorems.Thm_PI_CntNotIntW_piMap_one_tmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open scoped TensorProduct
open ValuativeRel
namespace PI.CntNotIntW
theorem _root_.solution : PiSurj := by
  unfold PiSurj
  intro K _ _ ℓ _ Fp _ _ _ _ _ _ hcont hfin ι hdense
  have : T2Space Fp := t2Space_of_nonarchimedeanLocalField' Fp
  have : FiniteDimensional ℚ_[ℓ] Fp := hfin
  have : ContinuousSMul ℚ_[ℓ] Fp := by
    constructor
    have h : (fun p : ℚ_[ℓ] × Fp => p.1 • p.2) = fun p => algebraMap ℚ_[ℓ] Fp p.1 * p.2 := by
      funext p
      exact Algebra.smul_def _ _
    rw [h]
    exact (hcont.comp continuous_fst).mul continuous_snd
  let S : Submodule ℚ_[ℓ] Fp := LinearMap.range (piMap K ℓ Fp ι).toLinearMap
  have hS : IsClosed (S : Set Fp) := S.closed_of_finiteDimensional
  have hsub : Set.range ι ⊆ (S : Set Fp) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨1 ⊗ₜ y, piMap_one_tmul K ℓ Fp ι y⟩
  intro z
  obtain ⟨w, hw⟩ := closure_minimal hsub hS (hdense z)
  exact ⟨w, hw⟩
end PI.CntNotIntW
