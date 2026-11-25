-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SchurClosable.Main.unitary_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:45:01.405025+00:00
-- url     : https://prove2.me/submissions/770e77c9-b9bb-4e8b-a081-5e17f184c561

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SchurClosable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurUnitaryInner_UnitaryInner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SchurClosable PI.UnitaryGroupMassFormula.SchurClosable.Main
open Filter Topology
namespace PI.UnitaryGroupMassFormula.SchurClosable.Main
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (hT : ∀ x, ‖T x‖ = ‖x‖) (x y : H) : inner ℂ (T x) (T y) = inner ℂ x y :=
  (⟨T.toLinearMap, hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y
end PI.UnitaryGroupMassFormula.SchurClosable.Main
