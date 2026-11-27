-- Prove2me | solution 1 for PI.VolStabW.freeOpen_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:19:27.43047+00:00
-- url     : https://prove2.me/submissions/a3541dd1-bd08-4c6d-8c02-e7e76a1a4c84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FibTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FreeOpen
import Theorems.Thm_PI_VolStabW_TensAllW_isOpen_linIndep
import Theorems.Thm_PI_VolStabW_TensAllW_lip_field
import Theorems.Thm_PI_VolStabW_isOpen_units_Ainf
import Theorems.Thm_PI_VolStabW_isOpen_units_Fv
import Theorems.Thm_PI_VolStabW_lip_ainf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW TensAllW
namespace PI.VolStabW
theorem _root_.solution : FreeOpen := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  refine ⟨isOpen_linIndep (Module.finBasis F E) (Ainf F) (isOpen_units_Ainf F) (lip_ainf F),
    fun v => ?_⟩
  exact isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv F v) (lip_field _)
end PI.VolStabW
