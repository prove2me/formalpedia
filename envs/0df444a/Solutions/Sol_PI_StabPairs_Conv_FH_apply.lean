-- Prove2me | solution 1 for PI.StabPairs.Conv.FH_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:53:47.421224+00:00
-- url     : https://prove2.me/submissions/770cba4b-9435-4afa-8deb-a7e75d4f2be1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_UtSubOneLast
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_HermBvecFvec

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
open PI PI.StabPairs PI.StabPairs.Conv
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
namespace PI.StabPairs.Conv
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ)
    (j : Fin (r + 1) ⊕ Fin (r + 1)) :
    (((Fm k r z z' γ)ᴴ * Hpk k r) *ᵥ v) j = herm (Hpk k r) v (gramVec k r z z' γ j) := by
  rw [← Matrix.mulVec_mulVec]
  rfl
end PI.StabPairs.Conv
