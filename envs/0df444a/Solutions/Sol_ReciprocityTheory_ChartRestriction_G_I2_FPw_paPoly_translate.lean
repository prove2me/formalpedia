-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.paPoly_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:01.365545+00:00
-- url     : https://prove2.me/submissions/1447c02f-93b8-4b76-addb-d2d4eff951b6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paMono_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paPoly_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paPoly_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paPoly_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paPoly_coord
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_paPoly_pow
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
private lemma prod_mem_paPoly (s : Finset ι) (f : ι → EuclideanSpace ℂ ι → ℂ) (d : ι → ℕ)
    (h : ∀ i ∈ s, f i ∈ paPoly (ι := ι) (d i)) : (∏ i ∈ s, f i) ∈ paPoly (∑ i ∈ s, d i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact paPoly_const (ι := ι) 1
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact paPoly_mul (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
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
theorem _root_.solution {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (a : EuclideanSpace ℂ ι) : (fun v => F (v - a)) ∈ paPoly c := by
  unfold paPoly at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    have hdeg := mem_paS'.mp hα
    have he : (fun v => paMono α (v - a)) =
        ∏ i, ((fun v : EuclideanSpace ℂ ι => v i) - fun _ => a i) ^ (α i) := by
      funext v
      simp [paMono_eq, Finset.prod_apply]
    rw [he]
    have hi : ∀ i, ((fun v : EuclideanSpace ℂ ι => v i) - fun _ => a i) ∈ paPoly (ι := ι) 1 :=
      fun i => Submodule.sub_mem _ (paPoly_coord i) (paPoly_mono (Nat.zero_le 1) (paPoly_const (a i)))
    have hle : ∑ i, α i * 1 ≤ c := by
      rw [finsupp_degree_eq_sum] at hdeg
      simpa using hdeg
    exact paPoly_mono hle (prod_mem_paPoly Finset.univ _ (fun i => α i * 1)
      fun i _ => paPoly_pow (hi i) (α i))
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul b x _ hx => exact Submodule.smul_mem _ b hx
end ReciprocityTheory.ChartRestriction.G.I2.FPw
