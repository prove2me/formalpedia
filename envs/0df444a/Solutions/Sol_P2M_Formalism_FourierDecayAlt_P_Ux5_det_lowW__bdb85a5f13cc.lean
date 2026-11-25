-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Ux5_det_lowW__bdb85a5f13cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:02.220135+00:00
-- url     : https://prove2.me/submissions/b89d320e-6759-4719-89cd-24eda76e1cac

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) : (lowW σ v).det = 1 := by
  have h : (lowW σ v).BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have : ¬ (j < i ∧ σ.symm j < σ.symm i) := fun h => absurd h.1 (not_lt.mpr (le_of_lt hij'))
    simp [lowW, ne_of_lt hij', this]
  rw [Matrix.det_of_isLowerTriangular _ h]
  simp [lowW]
end Formalism.FourierDecayAlt.P.Ux5
