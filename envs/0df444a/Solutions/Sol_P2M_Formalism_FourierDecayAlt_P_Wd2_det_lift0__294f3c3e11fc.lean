-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Wd2_det_lift0__294f3c3e11fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:06.40138+00:00
-- url     : https://prove2.me/submissions/44e9a1a9-552a-4209-84ce-beef03c26c1a

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_liftMatrix_eq_map_scalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_J_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_smulJ_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd2
theorem _root_.solution (M M' : M2 A) (c : K) (H : M * YangianSpanCharacter.T.J A * M'ᵀ = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (lift0 M')ᵀ = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]
end Formalism.FourierDecayAlt.P.Wd2
