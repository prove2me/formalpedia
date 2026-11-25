-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.moment_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:54.746221+00:00
-- url     : https://prove2.me/submissions/3db083f5-a699-40da-8643-6590ba9e6c78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_MomentMatch
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_moment_poly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (p : ℂ) :
    ∑ i ∈ univ.filter (fun i => b i = p), u i = ∑ s ∈ univ.filter (fun s => a s = p), r s := by
  classical
  set S : Finset ℂ := (univ.image b ∪ univ.image a).erase p with hS
  have hne : (∏ s ∈ S, (p - s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  let Q : ℂ[X] := C (∏ s ∈ S, (p - s))⁻¹ * ∏ s ∈ S, (X - C s)
  have hQ : ∀ x, x ∈ univ.image b ∪ univ.image a → Q.eval x = if x = p then 1 else 0 := by
    intro x hx
    simp only [Q, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with hxp
    · subst hxp
      exact inv_mul_cancel₀ hne
    · rw [Finset.prod_eq_zero (i := x) (Finset.mem_erase.mpr ⟨hxp, hx⟩) (sub_self x), mul_zero]
  have e := moment_poly b u a r h Q
  rw [Finset.sum_filter, Finset.sum_filter]
  calc ∑ i, (if b i = p then u i else 0) = ∑ i, u i * Q.eval (b i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [hQ (b i) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp
    _ = ∑ s, r s * Q.eval (a s) := e
    _ = _ := Finset.sum_congr rfl fun s _ => by
          rw [hQ (a s) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS
