-- Prove2me | solution 1 for PI.ZuckTensorWork.cjSub_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:54.339904+00:00
-- url     : https://prove2.me/submissions/4f7c25dd-d5d8-498c-8c8b-0117abd1b4ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_cjSub_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {n : ℕ}
namespace PI.ZuckTensorWork
theorem _root_.solution (S : Submodule ℂ H) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (cjSub S) := by
  classical
  obtain ⟨T, hT⟩ := (Submodule.fg_iff_finiteDimensional S).mpr inferInstance
  apply (Submodule.fg_iff_finiteDimensional _).mp
  refine ⟨T.image Cj.mk, ?_⟩
  rw [Finset.coe_image, ← cjSub_span, hT]
end PI.ZuckTensorWork
