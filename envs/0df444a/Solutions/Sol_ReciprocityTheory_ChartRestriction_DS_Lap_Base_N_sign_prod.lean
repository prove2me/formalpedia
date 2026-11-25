-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.sign_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:29.914933+00:00
-- url     : https://prove2.me/submissions/4a51bf99-55ea-4933-b55f-db33ad860880

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExistsCyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution {m : ℕ} (x : Fin m → ℝ) (hx : StrictAnti x) (s : Fin m) :
    0 < (-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j) := by
  classical
  have habs : ∀ j ∈ univ.erase s, |x s - x j| = (if j < s then -1 else 1) * (x s - x j) := by
    intro j hj
    have hjs : j ≠ s := Finset.ne_of_mem_erase hj
    split_ifs with h
    · have h1 : x s < x j := hx h
      rw [abs_of_neg (by linarith)]
      ring
    · have h2 : s < j := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hjs)
      have h1 : x j < x s := hx h2
      rw [abs_of_pos (by linarith)]
      ring
  have hc : ((univ.erase s).filter (fun j => j < s)).card = s.val := by
    have he : (univ.erase s).filter (fun j => j < s) = Finset.Iio s := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Iio]
      exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
    rw [he, Fin.card_Iio]
  have hprod : ∏ j ∈ univ.erase s, |x s - x j| = (-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j) := by
    rw [Finset.prod_congr rfl habs, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const, one_pow, mul_one, hc]
  rw [← hprod]
  exact Finset.prod_pos fun j hj =>
    abs_pos.2 (sub_ne_zero.2 (hx.injective.ne (Finset.ne_of_mem_erase hj).symm))
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
