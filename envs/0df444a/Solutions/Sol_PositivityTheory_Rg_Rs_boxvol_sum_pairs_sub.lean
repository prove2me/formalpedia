-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.boxvol.sum_pairs_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:19:42.548799+00:00
-- url     : https://prove2.me/submissions/112cbf4e-1cc8-4ce5-a9c5-7841f6db581b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_BoxVolumes_SumRangeSuccMulSubPred
import Theorems.Thm_PositivityTheory_Rg_Rs_boxvol_sum_range_pairs_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.boxvol
namespace PositivityTheory.Rg.Rs.boxvol
theorem _root_.solution (n : ℕ) (x : Fin n → ℝ) :
    ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (x p.1.1 - x p.1.2)
      = ∑ r ∈ Finset.range n, ((r : ℝ) * ((n : ℝ) - r)) *
          (if h : 0 < r ∧ r < n then x ⟨r - 1, by omega⟩ - x ⟨r, h.2⟩ else 0) := by
  set y : ℕ → ℝ := fun k => if h : k < n then x ⟨k, h⟩ else 0 with hy
  have hyx : ∀ i : Fin n, y i = x i := fun i => by simp [hy, i.2]
  have hL : ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (x p.1.1 - x p.1.2)
      = ∑ j ∈ range n, ∑ i ∈ range j, (y i - y j) := by
    rw [← Finset.sum_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
      (fun p : Fin n × Fin n => x p.1 - x p.2), Finset.sum_filter, Fintype.sum_prod_type_right,
      ← Fin.sum_univ_eq_sum_range (fun j => ∑ i ∈ range j, (y i - y j)) n]
    refine sum_congr rfl fun j _ => ?_
    have hj : range (j : ℕ) = (range n).filter (· < (j : ℕ)) := by
      ext i
      simp only [mem_range, mem_filter]
      have := j.2
      omega
    rw [hj, Finset.sum_filter,
      ← Fin.sum_univ_eq_sum_range (fun i => if i < (j : ℕ) then y i - y j else 0) n]
    refine sum_congr rfl fun i _ => ?_
    simp only [Fin.lt_def, hyx]
  rw [hL, sum_range_pairs_sub]
  refine sum_congr rfl fun r hr => ?_
  have hrn : r < n := mem_range.mp hr
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · simp
  · have h : 0 < r ∧ r < n := ⟨h0, hrn⟩
    have h1 : r - 1 < n := by omega
    simp [hy, h0, hrn, h1]
end PositivityTheory.Rg.Rs.boxvol
