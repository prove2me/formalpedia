-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paPoly_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:32.190696+00:00
-- url     : https://prove2.me/submissions/4f89bb12-6a58-400f-ac53-9c41b9501b9b

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
theorem _root_.solution (a : ℂ) : (fun _ : EuclideanSpace ℂ ι => a) ∈ paPoly 0 := by
  have h1 : paMono (0 : ι →₀ ℕ) = fun _ : EuclideanSpace ℂ ι => (1 : ℂ) := by
    funext v
    simp [paMono_eq]
  have h2 : (fun _ : EuclideanSpace ℂ ι => a) = a • paMono (0 : ι →₀ ℕ) := by
    rw [h1]
    funext v
    simp
  rw [h2]
  exact Submodule.smul_mem _ a (paMono_mem_paPoly_of_degree_le (by simp))
end ReciprocityTheory.ChartRestriction.G.I2.FPw
