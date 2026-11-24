-- Prove2me | solution 1 for PI.FrameInd.CountsW.diag_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:56:32.165799+00:00
-- url     : https://prove2.me/submissions/a19df98d-79d1-4fca-a8d2-4a1276b4bd01

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_NonposCount
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_Counts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.FrameInd PI.FrameInd.CountsW
open PI.FrameInd
namespace PI.FrameInd.CountsW
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A * (hA.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) := by
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h
end PI.FrameInd.CountsW
