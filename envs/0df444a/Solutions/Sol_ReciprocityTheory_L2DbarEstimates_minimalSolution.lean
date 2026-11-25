-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.minimalSolution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:36:47.158225+00:00
-- url     : https://prove2.me/submissions/816fc088-8d3c-4177-a4ff-a453f79ad5fd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolutionStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open scoped InnerProductSpace
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (E H : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] : MinimalSolutionStatement E H := by
  intro θ ℓ u u' hu h h'
  set R := LinearMap.range θ with hR
  have hw : u' - u ∈ Rᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro y ⟨e, rfl⟩
    rw [inner_sub_right, ← inner_conj_symm, h', ← inner_conj_symm, h, sub_self]
  have hcl : R.topologicalClosure ≤ Rᗮᗮ :=
    R.topologicalClosure_minimal R.le_orthogonal_orthogonal Rᗮ.isClosed_orthogonal
  have hperp : ∀ z ∈ R.topologicalClosure, ⟪u' - u, z⟫_ℂ = 0 := by
    intro z hz
    exact (Submodule.mem_orthogonal _ _).mp (hcl hz) _ hw
  refine ⟨hw, ?_, ?_⟩
  · have h0 : ⟪u, u' - u⟫_ℂ = 0 := by
      rw [← inner_conj_symm, hperp u hu, map_zero]
    have hsq : ‖u'‖ ^ 2 = ‖u‖ ^ 2 + ‖u' - u‖ ^ 2 := by
      have := @norm_add_sq ℂ H _ _ _ u (u' - u)
      rw [add_sub_cancel] at this
      rw [this, h0]
      simp
    have : ‖u‖ ^ 2 ≤ ‖u'‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg ‖u' - u‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  · intro hu'
    have hz : u' - u ∈ R.topologicalClosure := Submodule.sub_mem _ hu' hu
    have := hperp _ hz
    rw [inner_self_eq_zero, sub_eq_zero] at this
    exact this
end ReciprocityTheory.L2DbarEstimates
