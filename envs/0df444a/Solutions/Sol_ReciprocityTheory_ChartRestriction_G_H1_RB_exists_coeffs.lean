-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.RB.exists_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:47.056559+00:00
-- url     : https://prove2.me/submissions/ff33f17a-815a-42a5-ad72-744f66073e91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section phi
variable {d : ℕ} (u : Fin d → E) (k : Fin d)
private lemma exists_coeffs_of_mem_V {d : ℕ} (u : Fin d → E) {n : ℕ} {x : E} (hx : x ∈ V u n) :
    ∃ c : Fin d → ℝ, (∀ l : Fin d, n ≤ l.val → c l = 0) ∧ x = ∑ l, c l • u l := by
  rw [V, Finsupp.mem_span_image_iff_linearCombination] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨c, fun l hl => ?_, ?_⟩
  · by_contra h
    have := (Finsupp.mem_supported ℝ c).1 hc (Finsupp.mem_support_iff.2 h)
    exact absurd this (not_lt.2 hl)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    exact zero_smul _ _
end phi
end ReciprocityTheory.ChartRestriction.G.H1.RB
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace ReciprocityTheory.ChartRestriction.G.H1.RB
theorem _root_.solution {d : ℕ} (u : Fin d → E) {n : ℕ} {x : E} (hx : x ∈ V u n) :
    ∃ c : Fin d → ℝ, (∀ l : Fin d, n ≤ l.val → c l = 0) ∧ x = ∑ l, c l • u l := exists_coeffs_of_mem_V u hx
end ReciprocityTheory.ChartRestriction.G.H1.RB
