-- Prove2me | solution 1 for PI.VolStabW.rpGlue_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:39:34.180065+00:00
-- url     : https://prove2.me/submissions/b2cbbc58-178d-415b-bbfe-127cd734037a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
import Theorems.Thm_PI_VolStabW_RestrictedProductGluing_measurable_glue
import Theorems.Thm_PI_VolStabW_RestrictedProductGluing_glue_spec

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct
namespace PI.VolStabW
theorem _root_.solution : RPGlue := by
  intro F E _ _ _ _ _ M a d b
  exact ⟨RestrictedProductGluing.glue b, RestrictedProductGluing.measurable_glue b,
    fun p hp => RestrictedProductGluing.glue_spec b p hp⟩
end PI.VolStabW
