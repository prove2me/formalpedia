-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_dOp__sq_f46c3f4a63d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:52:05.08663+00:00
-- url     : https://prove2.me/submissions/38d8e0a9-5d04-4986-9653-5260e0a88dec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_sum_sq_zero_of_anti
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_car_anti_abs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
private theorem mem_plusIdx_iff_eq_true {ε : Fin n → Bool} {a : Fin n} :
    a ∈ plusIdx ε ↔ ε a = true := by
  simp [plusIdx]
private theorem mem_minusIdx_iff_eq_false {ε : Fin n → Bool} {a : Fin n} :
    a ∈ minusIdx ε ↔ ε a = false := by
  simp [minusIdx]
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E cp cm : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (hC : IsCAR cp cm)
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) : dOp' ε E cm * dOp' ε E cm = 0 := by
  have hsum : dOp' ε E cm =
      -∑ p ∈ plusIdx ε ×ˢ minusIdx ε, E p.1 p.2 * cm p.1 p.2 := by
    simp only [dOp', Finset.sum_product]
  rw [hsum, neg_mul_neg]
  apply car_sum_sq_zero_of_anti
  intro x hx y hy
  simp only [Finset.mem_product, mem_plusIdx_iff_eq_true, mem_minusIdx_iff_eq_false] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have n1 : x.2 ≠ y.1 := fun h => by simp [h, hy1] at hx2
  have n2 : y.2 ≠ x.1 := fun h => by simp [h, hx1] at hy2
  have hAB : E x.1 x.2 * E y.1 y.2 = E y.1 y.2 * E x.1 x.2 := by
    have h := hE x.1 x.2 y.1 y.2
    rw [if_neg n1, if_neg n2, sub_zero] at h
    exact sub_eq_zero.mp h
  exact car_anti_abs _ _ _ _ ((hEC y.1 y.2 x.1 x.2).2).symm ((hEC x.1 x.2 y.1 y.2).2).symm hAB
    (eq_neg_iff_add_eq_zero.mpr (hC x.1 x.2 y.1 y.2).2.1)
end ReciprocityTheory.ChartRestriction.DS
