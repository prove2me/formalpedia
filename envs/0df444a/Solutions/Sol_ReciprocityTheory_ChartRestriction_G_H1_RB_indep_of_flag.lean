-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.RB.indep_of_flag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:18.214467+00:00
-- url     : https://prove2.me/submissions/5a2edaf4-f300-4ef2-839d-4c51cc40ddac

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
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace ReciprocityTheory.ChartRestriction.G.H1.RB
theorem _root_.solution [FiniteDimensional ℝ E] {d : ℕ} (hd : d = finrank ℝ E) (f : Fin d → E)
    (h : ∀ k, f k ∉ V f k.val) : LinearIndependent ℝ f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  let s := Finset.univ.filter (fun l => g l ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [s, hi]⟩
  let k := s.max' hs
  have hk : g k ≠ 0 := by
    have := s.max'_mem hs
    simpa [s] using this
  have hgt : ∀ l, k < l → g l = 0 := by
    intro l hl
    by_contra h0
    exact absurd (s.le_max' l (by simp [s, h0])) (not_le.2 hl)
  have hsplit : ∀ l, g l • f l =
      (if l = k then g k • f k else 0) + (if l < k then g l • f l else 0) := by
    intro l
    rcases lt_trichotomy l k with h1 | h1 | h1
    · simp [h1, h1.ne]
    · rw [h1]; simp
    · simp [hgt l h1, h1.ne', not_lt.2 h1.le]
  have h2 : g k • f k + ∑ l ∈ Finset.univ.filter (· < k), g l • f l = 0 := by
    have e : ∑ l, g l • f l = g k • f k + ∑ l ∈ Finset.univ.filter (· < k), g l • f l := by
      rw [Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => hsplit l), Finset.sum_add_distrib,
        Finset.sum_filter]
      simp
    rw [← e]
    exact hg
  have hmem : g k • f k ∈ V f k.val := by
    rw [eq_neg_of_add_eq_zero_left h2]
    refine Submodule.neg_mem _ (_root_.sum_mem fun l hl => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, ?_, rfl⟩))
    have hl' : l < k := by simpa using hl
    exact Fin.lt_iff_val_lt_val.1 hl'
  have h3 := Submodule.smul_mem (V f k.val) (g k)⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ hk, one_smul] at h3
  exact h k h3
end ReciprocityTheory.ChartRestriction.G.H1.RB
