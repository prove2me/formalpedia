-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.norm_periodic_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:33:18.875449+00:00
-- url     : https://prove2.me/submissions/cc72437f-cd3b-4a43-a478-47d6b8d41f46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnFrameA

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
theorem _root_.solution (f : (Fin N → ℂ) → ℂ) (hf : Differentiable ℂ f) (L : AddSubgroup (Fin N → ℂ))
    (K : Set (Fin N → ℂ)) (hK : IsCompact K) (hcov : ∀ z, ∃ w ∈ K, z - w ∈ L)
    (hper : ∀ z, ∀ l ∈ L, ‖f (z + l)‖ = ‖f z‖) (z w : Fin N → ℂ) : f z = f w := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  apply hf.apply_eq_apply_of_bounded
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro _ ⟨u, rfl⟩
  obtain ⟨v, hv, hvu⟩ := hcov u
  have h := hper v (u - v) hvu
  have e : v + (u - v) = u := by abel
  rw [e] at h
  rw [h]
  exact hC v hv
end ReciprocityTheory.ChartRestriction.G.PullbackSections
