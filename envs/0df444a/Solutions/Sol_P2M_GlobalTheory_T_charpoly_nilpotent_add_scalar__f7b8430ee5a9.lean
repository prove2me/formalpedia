-- Prove2me | solution 1 for P2M_GlobalTheory_T_charpoly_nilpotent_add_scalar__f7b8430ee5a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:34:27.161141+00:00
-- url     : https://prove2.me/submissions/53a84ffe-5810-4c44-b291-20d1ae94ad1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyNilpotentAddScalar
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyNilpotentAddScalarStatement
import Theorems.Thm_GlobalTheory_charpoly_nilpotent_add_scalar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by
  first | exact @GlobalTheory.charpoly_nilpotent_add_scalar | exact GlobalTheory.charpoly_nilpotent_add_scalar | (intros; apply GlobalTheory.charpoly_nilpotent_add_scalar <;> assumption)
end _root_.GlobalTheory.T
