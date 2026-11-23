-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.not_injective_shift_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:02.433473+00:00
-- url     : https://prove2.me/submissions/1cecb49b-aa70-4c55-ba0f-6824abafc861

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {μ ν : Fin n → ℝ} (hμ : Function.Injective μ) (s : Fin n) (c : ℝ)
    (hs : ν s = μ s + c) (ho : ∀ x, x ≠ s → ν x = μ x) :
    ¬ Function.Injective ν ↔ ∃ s' ∈ univ.erase s, μ s + c = μ s' := by
  constructor
  · intro h
    simp only [Function.Injective, not_forall] at h
    obtain ⟨x, y, hxy, hne⟩ := h
    by_cases hx : x = s
    · subst hx
      refine ⟨y, by simp [Ne.symm hne], ?_⟩
      rw [← hs, hxy, ho y (Ne.symm hne)]
    · by_cases hy : y = s
      · subst hy
        refine ⟨x, by simp [hx], ?_⟩
        rw [← hs, ← hxy, ho x hx]
      · exact absurd (hμ (by rw [← ho x hx, ← ho y hy, hxy])) hne
  · rintro ⟨s', hs', h⟩ hinj
    have hne : s' ≠ s := (Finset.mem_erase.mp hs').1
    exact hne (hinj (by rw [ho s' hne, hs, h]))
end ReciprocityTheory.ChartRestriction.DS
