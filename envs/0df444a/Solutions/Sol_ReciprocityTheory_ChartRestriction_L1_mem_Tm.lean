-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.mem_Tm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:16.271674+00:00
-- url     : https://prove2.me/submissions/9b5b1a29-b42a-4968-9d0f-0702c9ce95ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {m : ℕ} (hm : 0 < m) (t : ℕ × ℕ × ℕ) :
    t ∈ Tm m ↔ t.1 * t.2.2 = m ∧ t.2.1 < t.2.2 := by
  rw [Tm, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hx, rfl⟩
    rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range] at hx
    exact ⟨Nat.mul_div_cancel' hx.1.1, hx.2⟩
  · obtain ⟨a, b, e⟩ := t
    rintro ⟨h1, h2⟩
    simp only at h1 h2
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have he : m / a = e := by rw [← h1, Nat.mul_div_cancel_left _ ha]
    refine ⟨⟨a, b⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
      exact ⟨⟨⟨e, h1.symm⟩, hm.ne'⟩, by rw [he]; exact h2⟩
    · simp only [he]
end ReciprocityTheory.ChartRestriction.L1
