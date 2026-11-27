-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.moment_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:26:35.500851+00:00
-- url     : https://prove2.me/submissions/4be14e07-f02f-4a4d-b74d-3d1c35b1a7e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_MomentMatch
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_moment_fibre

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ι : Type*} [Fintype ι] (b : ι → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (a : Fin n → ℂ)
    (ha : Function.Injective a) (r : Fin n → ℂ)
    (h : ∀ k : ℕ, ∑ i, (w i : ℂ) * b i ^ k = ∑ s, r s * a s ^ k) :
    (∀ i, ∃ s, b i = a s) ∧ ∀ s, r s = ∑ i ∈ univ.filter (fun i => b i = a s), (w i : ℂ) := by
  classical
  refine ⟨fun i => ?_, fun s => ?_⟩
  · by_contra hcon
    push_neg at hcon
    have e := moment_fibre b (fun i => (w i : ℂ)) a r h (b i)
    have e0 : univ.filter (fun s => a s = b i) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun t _ h' => hcon t h'.symm
    rw [e0, Finset.sum_empty] at e
    have hpos : 0 < ∑ j ∈ univ.filter (fun j => b j = b i), w j :=
      Finset.sum_pos (fun j _ => hw j) ⟨i, by simp⟩
    have e' : ((∑ j ∈ univ.filter (fun j => b j = b i), w j : ℝ) : ℂ) = 0 := by
      push_cast
      exact e
    exact hpos.ne' (by exact_mod_cast e')
  · have e := moment_fibre b (fun i => (w i : ℂ)) a r h (a s)
    have e1 : univ.filter (fun t => a t = a s) = {s} := by
      ext t
      simp [ha.eq_iff]
    rw [e1, Finset.sum_singleton] at e
    exact e.symm
end ReciprocityTheory.ChartRestriction.DS
