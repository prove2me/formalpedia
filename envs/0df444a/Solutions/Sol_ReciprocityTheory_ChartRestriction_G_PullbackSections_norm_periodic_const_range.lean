-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:04.48335+00:00
-- url     : https://prove2.me/submissions/f2005ff7-9b67-4cf5-a44d-aef34d3e9790

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnFrameA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_norm_periodic_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_exists_compact_reps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
variable {N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {La : Type} [AddCommGroup La] (P : La →+ (Fin N → ℂ))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (f : (Fin N → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z a, ‖f (z + P a)‖ = ‖f z‖) (z w : Fin N → ℂ) : f z = f w := by
  obtain ⟨K, hK, hcov⟩ := exists_compact_reps P hspan
  refine norm_periodic_const f hf P.range K hK hcov ?_ z w
  rintro u _ ⟨c, rfl⟩
  exact hper u c
end ReciprocityTheory.ChartRestriction.G.PullbackSections
