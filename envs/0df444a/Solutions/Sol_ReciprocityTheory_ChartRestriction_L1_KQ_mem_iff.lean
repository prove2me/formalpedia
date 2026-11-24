-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.KQ_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:00:09.055675+00:00
-- url     : https://prove2.me/submissions/9bc6395c-282c-4532-92f9-7989431d0e05

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQuadInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (d : ℕ) (z : ℂ) : z ∈ KQ d ↔ ∃ u v : ℚ, z = u + v * sqD d := by
  constructor
  · intro hz
    have h1 : z ∈ (KQ d).toSubalgebra := hz
    clear hz
    unfold KQ at h1
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (sqD_isIntegral d).isAlgebraic] at h1
    induction h1 using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
    | algebraMap r => exact ⟨r, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, v, rfl⟩ := hx
      obtain ⟨u', v', rfl⟩ := hy
      exact ⟨u + u', v + v', by push_cast; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, v, rfl⟩ := hx
      obtain ⟨u', v', rfl⟩ := hy
      refine ⟨u * u' - d * v * v', u * v' + v * u', ?_⟩
      have hs := sqD_sq d
      push_cast
      linear_combination (v * v') * hs
  · rintro ⟨u, v, rfl⟩
    have hs : sqD d ∈ KQ d := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    refine add_mem ?_ (mul_mem ?_ hs)
    · simp
    · simp
end ReciprocityTheory.ChartRestriction.L1
