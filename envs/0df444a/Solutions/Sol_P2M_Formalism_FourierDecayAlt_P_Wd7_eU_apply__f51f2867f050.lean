-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Wd7_eU_apply__f51f2867f050
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:46:22.899225+00:00
-- url     : https://prove2.me/submissions/4cbb551b-3f45-4c7b-9919-b9e462e73ffe

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd7_cond_iff__d5515724d8c4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if y a = j ∧ x = Function.update y a i then 1 else 0 := by
  unfold eU
  simp only [Matrix.of_apply]
  exact if_congr (cond_iff' a i j x y) rfl rfl
end Formalism.FourierDecayAlt.P.Wd7
