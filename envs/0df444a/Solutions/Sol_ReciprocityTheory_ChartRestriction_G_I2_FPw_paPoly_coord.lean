-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paPoly_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:50.787504+00:00
-- url     : https://prove2.me/submissions/bf5a325f-b36b-46e2-866d-7ab2bf6ad45f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paMono_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
private lemma finsupp_apply_le_degree (α : ι →₀ ℕ) (i : ι) : α i ≤ α.degree := by
  unfold Finsupp.degree
  by_cases h : i ∈ α.support
  · exact Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) h
  · have h0 : α i = 0 := by simpa [Finsupp.mem_support_iff] using h
    rw [h0]
    exact Nat.zero_le _
private lemma mem_paS' {c : ℕ} {α : ι →₀ ℕ} : α ∈ paS (ι := ι) c ↔ α.degree ≤ c := by
  simp only [paS, Finset.mem_filter, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_range,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨⟨α, fun i => ?_, ?_⟩, h⟩
    · have := finsupp_apply_le_degree α i
      omega
    · simp
private lemma finsupp_degree_eq_sum (α : ι →₀ ℕ) : α.degree = ∑ i, α i := by
  unfold Finsupp.degree
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
private lemma paMono_mem_paPoly_of_degree_le {c : ℕ} {α : ι →₀ ℕ} (h : α.degree ≤ c) :
    paMono α ∈ paPoly (ι := ι) c := by
  unfold paPoly
  exact Submodule.subset_span ⟨α, mem_paS'.mpr h, rfl⟩
end
end ReciprocityTheory.ChartRestriction.G.I2.FPw
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (i : ι) : (fun v : EuclideanSpace ℂ ι => v i) ∈ paPoly 1 := by
  have h1 : (fun v : EuclideanSpace ℂ ι => v i) = paMono (Finsupp.single i 1) := by
    funext v
    rw [paMono_eq, Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, hb, Ne.symm hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [h1]
  exact paMono_mem_paPoly_of_degree_le (le_of_eq (by rw [finsupp_degree_eq_sum]; simp [Finsupp.single_apply]))
end ReciprocityTheory.ChartRestriction.G.I2.FPw
