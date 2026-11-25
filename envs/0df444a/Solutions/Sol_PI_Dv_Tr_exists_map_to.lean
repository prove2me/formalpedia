-- Prove2me | solution 1 for PI.Dv.Tr.exists_map_to
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:13.442392+00:00
-- url     : https://prove2.me/submissions/4c4ae50c-26b4-4212-b4a6-6456ccc1c48b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
namespace PI.Dv.Tr
theorem _root_.solution (w0 w : W) (hw0 : w0 ≠ 0) : ∃ X : Module.End K W, X w0 = w := by
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual K W, f w0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w0).mp h)
  refine ⟨((f w0)⁻¹ • f).smulRight w, ?_⟩
  rw [LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf, one_smul]
end PI.Dv.Tr
