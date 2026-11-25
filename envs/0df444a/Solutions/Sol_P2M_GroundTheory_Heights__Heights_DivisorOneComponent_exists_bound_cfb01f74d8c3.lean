-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DivisorOneComponent_exists_bound_cfb01f74d8c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:10:49.926341+00:00
-- url     : https://prove2.me/submissions/f6f37b9f-e8e1-47bb-a2bb-e532a933d81e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceMultGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorOneComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorOneComponent
namespace GroundTheory.Heights₂.Heights.DivisorOneComponent
theorem _root_.solution (d : ℕ) : ∃ N : WithBot ℕ∞, N < (d : WithBot ℕ∞) ∧
    ∀ x : WithBot ℕ∞, x + 1 ≤ (d : WithBot ℕ∞) → x ≤ N := by
  rcases d with _ | k
  · refine ⟨⊥, WithBot.bot_lt_coe _, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe y =>
      have : y + 1 ≤ 0 := by exact_mod_cast hx
      simp at this
  · refine ⟨(k : WithBot ℕ∞), by exact_mod_cast Nat.lt_succ_self k, fun x hx => ?_⟩
    cases x using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe y =>
      have h1 : y + 1 ≤ ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast hx
      have h2 : y ≤ (k : ℕ∞) := by
        cases y using ENat.recTopCoe with
        | top => simp at h1
        | coe y =>
          have h3 : y + 1 ≤ k + 1 := by exact_mod_cast h1
          exact_mod_cast (by omega : y ≤ k)
      exact_mod_cast h2
end GroundTheory.Heights₂.Heights.DivisorOneComponent
