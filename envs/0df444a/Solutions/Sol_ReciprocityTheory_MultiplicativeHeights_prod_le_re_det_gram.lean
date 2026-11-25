-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.prod_le_re_det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:14:33.442781+00:00
-- url     : https://prove2.me/submissions/ced9fbd5-771f-4fdb-8553-d3a887cab1dc

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_DetGramEqProdGramSchmidt
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_det_gram_eq_prod_gramSchmidt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
open Finset InnerProductSpace
private theorem exists_eq_gramSchmidt_add_sum_Iio {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (n : ℕ) (v : Fin n → E) :
    ∃ c : Fin n → Fin n → ℂ,
      ∀ j, v j = gramSchmidt ℂ v j + ∑ i ∈ Iio j, c j i • gramSchmidt ℂ v i :=
  ⟨_, fun j => gramSchmidt_def'' (𝕜 := ℂ) v j⟩
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Finset InnerProductSpace
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) (δ : Fin n → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (h : ∀ k, ∀ x ∈ Submodule.span ℂ (v '' Set.Iio k), δ k ≤ ‖v k - x‖ ^ 2) :
    ∏ k, δ k ≤ (Matrix.gram ℂ v).det.re := by
  classical
  rw [det_gram_eq_prod_gramSchmidt, ← Complex.ofReal_prod, Complex.ofReal_re]
  refine Finset.prod_le_prod (fun k _ => hδ k) (fun k _ => ?_)
  obtain ⟨c, hc⟩ := exists_eq_gramSchmidt_add_sum_Iio n v
  have hmem : ∑ i ∈ Iio k, c k i • gramSchmidt ℂ v i ∈ Submodule.span ℂ (v '' Set.Iio k) := by
    rw [← span_gramSchmidt_Iio (𝕜 := ℂ) v k]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)
  have h1 := h k _ hmem
  rwa [← eq_sub_of_add_eq (hc k).symm] at h1
end ReciprocityTheory.MultiplicativeHeights
