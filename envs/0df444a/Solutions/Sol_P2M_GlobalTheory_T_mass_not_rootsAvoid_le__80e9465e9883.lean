-- Prove2me | solution 1 for P2M_GlobalTheory_T_mass_not_rootsAvoid_le__80e9465e9883
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:49.832583+00:00
-- url     : https://prove2.me/submissions/681ae18d-cd30-4902-8bc9-9a111d995ca2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLeStatement
import Theorems.Thm_GlobalTheory_BadShare_mass_not_rootsAvoid_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) [Fact g.Prime], ∀ (N q d : ℕ) (c : (ZMod g)ˣ), (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → (mass g N fun f => ¬ RootsAvoid g c f) ≤ 1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1) := by
  first | exact @GlobalTheory.BadShare.mass_not_rootsAvoid_le | exact GlobalTheory.BadShare.mass_not_rootsAvoid_le | (intros; apply GlobalTheory.BadShare.mass_not_rootsAvoid_le <;> assumption)
end _root_.GlobalTheory.T
