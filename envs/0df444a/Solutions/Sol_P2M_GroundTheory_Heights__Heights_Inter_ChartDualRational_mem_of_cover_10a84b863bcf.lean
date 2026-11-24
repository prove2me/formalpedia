-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_of_cover_10a84b863bcf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:18.217059+00:00
-- url     : https://prove2.me/submissions/8fb1b647-fad4-4ec1-91df-d7843ed28dc3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDualRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDualRational
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_exists_uniform_cde85cdc1d96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_pow_mul_mem_mono_5061ec5b9960

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open GroundTheory.Heights₂.Heights.Inter.ChartDualRational
variable {Ω : Type*} [Field Ω] {R : Subalgebra ℤ Ω}
namespace GroundTheory.Heights₂.Heights.Inter.ChartDualRational
theorem _root_.solution {k : ℕ} {f c : Fin k → Ω} (hf : ∀ l, f l ∈ R) (hc : ∀ l, c l ∈ R) (hsum : ∑ l, c l * f l = 1)
    {y : Ω} (hy : ∀ l, ∃ N : ℕ, f l ^ N * y ∈ R) : y ∈ R := by
  obtain ⟨N, hN⟩ := exists_uniform _ (fun l _ _ h ↦ pow_mul_mem_mono (hf l) h) hy
  let f' : Fin k → R := fun l ↦ ⟨f l, hf l⟩
  have htop : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : ∑ l, (⟨c l, hc l⟩ : R) * f' l = 1 := Subtype.ext (by simpa [f'] using hsum)
    rw [← h1]
    exact Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have hN' := Ideal.span_pow_eq_top _ htop N
  rw [← Set.range_comp, Ideal.eq_top_iff_one] at hN'
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hN'
  have hd' : ∑ l, (d l : Ω) * f l ^ N = 1 := by simpa [f'] using congrArg Subtype.val hd
  have : y = ∑ l, (d l : Ω) * (f l ^ N * y) := by
    simp_rw [← mul_assoc, ← Finset.sum_mul, hd', one_mul]
  rw [this]
  exact sum_mem fun l _ ↦ mul_mem (d l).2 (hN l)
end GroundTheory.Heights₂.Heights.Inter.ChartDualRational
