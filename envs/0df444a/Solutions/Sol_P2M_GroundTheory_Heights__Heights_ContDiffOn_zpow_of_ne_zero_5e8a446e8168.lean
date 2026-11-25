-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ContDiffOn_zpow_of_ne_zero_5e8a446e8168
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:26:47.150329+00:00
-- url     : https://prove2.me/submissions/7a03d169-ff15-46b1-b521-79c01b4ed1a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MemPointsOfGeneratorsVanish

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
open MvPolynomial
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ContDiffOn
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {s : Set E} (hf : ContDiffOn ℝ ∞ f s) (h0 : ∀ x ∈ s, f x ≠ 0) (m : ℤ) :
    ContDiffOn ℝ ∞ (fun x ↦ f x ^ m) s := by
  cases m with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv fun x hx ↦ pow_ne_zero _ (h0 x hx)
end ContDiffOn
end GroundTheory.Heights₂.Heights
