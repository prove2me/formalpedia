-- Prove2me | solution 1 for PIW.AdelClassFin.stDict_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:24:25.191959+00:00
-- url     : https://prove2.me/submissions/eddcb23f-406b-49ee-8f70-1b1b34b813b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (h1 : MLat) (h2 : MDual) (h3 : MInj) (h4 : MEquiv) : StDict :=
  fun I => ⟨abelian₂ I, fun x => ⟨(h1 I x).1, (h1 I x).2, h2 I x⟩, h3 I, h4 I⟩
end PIW.AdelClassFin
