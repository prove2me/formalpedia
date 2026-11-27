-- Prove2me | solution 1 for P2M_GlobalTheory_T_finite_fibre_and_eq_of_specializes_of_isFinite__bb3d4a10e7ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:51:56.484628+00:00
-- url     : https://prove2.me/submissions/40ba2824-0f04-42c9-9bca-f95a5f5e91dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFibreAndEqOfSpecializesOfIsFinite
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFibreAndEqOfSpecializesOfIsFiniteStatement
import Theorems.Thm_GlobalTheory_finite_fibre_and_eq_of_specializes_of_isFinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y Y' : Scheme.{0}) (k : Y' ⟶ Y), IsFinite k → ∀ y : Y, {a : Y' | k a = y}.Finite ∧ ∀ a b : Y', k a = y → k b = y → a ⤳ b → a = b := by
  first | exact @GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite | exact GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite | (intros; apply GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite <;> assumption)
end _root_.GlobalTheory.T
