-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_Wd1_eU_apply__48c6d160d783
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:51:13.757313+00:00
-- url     : https://prove2.me/submissions/eae609de-0ae4-4731-896e-d005018e0fd5

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd1_cond_iff__300993909eb5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd1
open Matrix Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd1
theorem _root_.solution (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if y a = j ∧ x = Function.update y a i then 1 else 0 := by
  simp only [eU, Matrix.of_apply]
  exact if_congr (cond_iff' a i j x y) rfl rfl
end Formalism.FourierDecayAlt.P.Wd1
