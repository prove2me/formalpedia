-- Prove2me | solution 1 for PI.StabPairsW.det_UT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:56:27.510196+00:00
-- url     : https://prove2.me/submissions/814f7056-c6d8-4a9a-9b69-058f50de2550

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
theorem _root_.solution {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ UTset m) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => hu.1 i j hij)]
  simp [hu.2]
end PI.StabPairsW
