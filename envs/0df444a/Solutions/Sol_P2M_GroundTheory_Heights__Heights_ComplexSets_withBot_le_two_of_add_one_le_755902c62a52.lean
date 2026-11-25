-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_withBot_le_two_of_add_one_le_755902c62a52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:08.353845+00:00
-- url     : https://prove2.me/submissions/986b2f51-4d03-41cd-ac73-da7d80b3cab1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution (x : WithBot ℕ∞) (hx : x + 1 ≤ 3) : x ≤ 2 := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd hx (by decide)
    | coe k =>
      have h1 : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((3 : ℕ) : WithBot ℕ∞) := by simpa using hx
      have h2 : k + 1 ≤ 3 := by exact_mod_cast h1
      have h3 : ((k : ℕ) : WithBot ℕ∞) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast (show k ≤ 2 by omega)
      simpa using h3
end GroundTheory.Heights₂.Heights.ComplexSets
