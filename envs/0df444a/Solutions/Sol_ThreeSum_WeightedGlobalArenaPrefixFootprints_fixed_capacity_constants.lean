-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPrefixFootprints.fixed_capacity_constants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T21:56:07.259482+00:00
-- url     : https://prove2.me/submissions/83531220-5341-4a95-b4a9-140742f092d5

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairMass
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaCapacity
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Definitions.Def_Submission_Weighted_Global_TernaryMomentChannelResources
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPrefixFootprints_fixed_capacity_all

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrefixFootprints
open WeightedGlobalArenaLayout WeightedGlobalArenaPairMass WeightedGlobalSignedPadding
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

open Lean Elab Tactic Meta
namespace ThreeSum.WeightedGlobalArenaPrefixFootprints
theorem _root_.solution {p m F M b : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (τ cap K H drift scale : ℕ)
    (hM : 1<M) (hb : 1<b) :
    ∃ D E : ℕ, E≤D ∧ ∀ n U j, j≤Nat.clog M (n^2) →
      envelope maps τ cap M b K H drift scale n U j≤capacity D E (n+U) := by
  obtain ⟨D,E,h⟩ := fixed_capacity_all maps τ cap K H drift scale hM hb
  refine ⟨D+E,E,by omega,fun n U j hj => (h n U j hj).trans ?_⟩
  unfold capacity
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
end ThreeSum.WeightedGlobalArenaPrefixFootprints
