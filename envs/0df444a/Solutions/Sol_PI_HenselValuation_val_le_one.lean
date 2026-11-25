-- Prove2me | solution 1 for PI.HenselValuation.val_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:06.028113+00:00
-- url     : https://prove2.me/submissions/7f2d05f2-dfdc-492d-bf4d-605c73777bd7

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
theorem _root_.solution (x : 𝒪[F]) : valuation F (x : F) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp x.2
end PI.HenselValuation
