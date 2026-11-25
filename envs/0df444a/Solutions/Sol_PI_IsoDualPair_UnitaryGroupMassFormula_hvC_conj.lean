-- Prove2me | solution 1 for PI.IsoDualPair.UnitaryGroupMassFormula.hvC_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:44:43.272613+00:00
-- url     : https://prove2.me/submissions/35d64de5-73c0-4cbd-9963-bc306003b171

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.IsoDualPair PI.IsoDualPair.UnitaryGroupMassFormula
open PI.IsoDualPair
variable {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoDualPair.UnitaryGroupMassFormula
theorem _root_.solution (x : Lt → Fin N → ℕ → ℂ) :
    (fun J => conj (hvC N nu x J)) = hvC N nu (fun s a j => conj (x s a j)) := by
  funext J
  simp only [hvC, minY, map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  rfl
end PI.IsoDualPair.UnitaryGroupMassFormula
