-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.locallyCompactSpace_of_isLocalHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:17:59.795668+00:00
-- url     : https://prove2.me/submissions/4458b21b-66f0-44a8-8c86-af4f6e67735a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocallyCompactSpaceOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ)
    (z : M → V n) (hz : IsLocalHomeomorph z) : LocallyCompactSpace M := by
  have : ∀ x : M, ∃ e : OpenPartialHomeomorph M (V n), x ∈ e.source := fun x =>
    let ⟨e, hx, _⟩ := hz x; ⟨e, hx⟩
  choose c hc using this
  have hb : ∀ x : M, (𝓝 x).HasBasis
      (fun s ↦ s ∈ 𝓝 (c x x) ∧ IsCompact s ∧ s ⊆ (c x).target)
      fun s ↦ (c x).symm '' s := fun x ↦ by
    rw [← (c x).symm_map_nhds_eq (hc x)]
    exact ((compact_basis_nhds (c x x)).hasBasis_self_subset
      ((c x).open_target.mem_nhds ((c x).map_source (hc x)))).map _
  refine .of_hasBasis hb ?_
  rintro x s ⟨_, h₂, h₃⟩
  exact h₂.image_of_continuousOn ((c x).continuousOn_symm.mono h₃)
end ReciprocityTheory.L2DbarEstimates.I
