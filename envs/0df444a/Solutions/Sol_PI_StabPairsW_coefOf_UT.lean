-- Prove2me | solution 1 for PI.StabPairsW.coefOf_UT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:44.069548+00:00
-- url     : https://prove2.me/submissions/66793ff9-48dc-41a8-a0df-d7024feed949

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution (y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    (Matrix.of fun a b => coefOf (k := k) b (y b) a) ∈ UTset (r + 1) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · simp only [Matrix.of_apply, coefOf, if_neg hab.ne']
    rw [dif_neg (fun h => lt_asymm h (Fin.lt_def.1 hab))]
  · simp [coefOf]
end PI.StabPairsW
