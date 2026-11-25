-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_PolyMaxLowerBound_exists_pos_le_cb4257d68214
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:25.905133+00:00
-- url     : https://prove2.me/submissions/e08648d5-c907-41c1-8e62-9fbc9bc7300f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PPolyMaxLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Set
open ReciprocityTheory.AnForm.A (polyMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace PolyMaxLowerBound
theorem _root_.solution {n : ℕ} (f : Fin n → ℝ) (hf : ∀ j, 0 < f j) :
    ∃ δ, 0 < δ ∧ ∀ j, δ ≤ f j := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
  · obtain ⟨j₀, hj₀⟩ := Finite.exists_min f
    exact ⟨f j₀, hf j₀, hj₀⟩
end PolyMaxLowerBound
end GroundTheory.Heights₂.Heights.Regular
