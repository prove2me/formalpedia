-- Prove2me | solution 1 for P2M_GlobalTheory_T_commute_of_commute_of_charpoly_separable__57f86e3e92f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:21.597445+00:00
-- url     : https://prove2.me/submissions/ec984592-46e1-458f-8b3c-5b7d78191b33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommuteOfCommuteSeparableCharpoly
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommuteOfCommuteSeparableCharpolyStatement
import Theorems.Thm_GlobalTheory_commute_of_commute_separable_charpoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (n : ℕ) (y a b : Matrix (Fin n) (Fin n) K), y.charpoly.Separable → a * y = y * a → b * y = y * b → a * b = b * a := by
  first | exact @GlobalTheory.commute_of_commute_separable_charpoly | exact GlobalTheory.commute_of_commute_separable_charpoly | (intros; apply GlobalTheory.commute_of_commute_separable_charpoly <;> assumption)
end _root_.GlobalTheory.T
