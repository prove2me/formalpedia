-- Prove2me | solution 1 for PIW.AdelClassFin.dictTop_map_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:35.571966+00:00
-- url     : https://prove2.me/submissions/86c11578-4280-458f-a81d-c136587ce25e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictTop

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
theorem _root_.solution (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) I.E) (w : Fin I.n → I.E) :
    M.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ iv I w = iv I (M *ᵥ w) := by
  funext i
  exact (RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) M w i).symm
end PIW.AdelClassFin
