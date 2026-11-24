-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_SignAntidiagonal_neg_one_sq__ee10da71c303
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:28.914339+00:00
-- url     : https://prove2.me/submissions/9165e985-7cac-4c93-a941-ff7b5f980dc6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (s : ℕ) : ((-1 : ℂ) ^ s) * ((-1) ^ s) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num
end Formalism.FourierDecayAlt.P.SignAntidiagonal
