-- Prove2me | solution 1 for PI.HenselValuation.continuous_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:49.222234+00:00
-- url     : https://prove2.me/submissions/086d1fbf-a976-4560-9569-ce687efc04f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Hensel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HenselOpenValuation_IsOpenLeVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Polynomial Topology
open PI PI.HenselValuation
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace PI.HenselValuation
theorem _root_.solution (f : Polynomial 𝒪[F]) :
    Continuous fun y : 𝒪[F] => ((f.eval y : 𝒪[F]) : F) :=
  continuous_subtype_val.comp f.continuous
end PI.HenselValuation
