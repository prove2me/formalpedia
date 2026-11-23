-- Prove2me | solution 1 for PI.VolSemiDirect.W.Lc.finite_nf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:19.67216+00:00
-- url     : https://prove2.me/submissions/70fc0dd2-50a7-4be8-9f53-9f4510856155

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolSemiDirect
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_TensTopOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Lc
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
namespace PI.VolSemiDirect.W.Lc
theorem _root_.solution (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Module.Finite F E :=
  Module.Finite.of_restrictScalars_finite ℚ F E
end PI.VolSemiDirect.W.Lc
