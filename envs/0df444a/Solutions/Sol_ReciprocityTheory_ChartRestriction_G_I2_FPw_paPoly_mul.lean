-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paPoly_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:50.081809+00:00
-- url     : https://prove2.me/submissions/8cd66bcf-3b4b-4889-8c09-053761b54ee1

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
private lemma paMono_mul (α β : ι →₀ ℕ) :
    paMono α * paMono β = paMono (ι := ι) (α + β) := by
  funext v
  simp only [Pi.mul_apply, paMono_eq, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
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
theorem _root_.solution {c d : ℕ} {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (hG : G ∈ paPoly d) :
    F * G ∈ paPoly (c + d) := by
  unfold paPoly at hF hG ⊢
  have hm := Submodule.mul_mem_mul hF hG
  rw [Submodule.span_mul_span] at hm
  refine Submodule.span_le.mpr (Set.mul_subset_iff.mpr ?_) hm
  rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
  rw [paMono_mul]
  refine Submodule.subset_span ⟨α + β, mem_paS'.mpr ?_, rfl⟩
  rw [map_add]
  exact add_le_add (mem_paS'.mp hα) (mem_paS'.mp hβ)
end ReciprocityTheory.ChartRestriction.G.I2.FPw
