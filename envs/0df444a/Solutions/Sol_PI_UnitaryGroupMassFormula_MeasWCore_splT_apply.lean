-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.MeasWCore.splT_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:37.002191+00:00
-- url     : https://prove2.me/submissions/47ce4570-90ce-44a5-a4a9-719aa5bbec54

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_Measures
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedMeasureSplitting_SplTApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.MeasWCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.MeasWCore
theorem _root_.solution (x : AF F ⊗[F] E) :
    splT x = (tensMap (E := E) (fstA F) x, tensMap (E := E) (sndA F) x) := rfl
end PI.UnitaryGroupMassFormula.MeasWCore
