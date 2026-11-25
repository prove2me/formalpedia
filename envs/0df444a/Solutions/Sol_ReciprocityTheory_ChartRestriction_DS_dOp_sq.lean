-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dOp_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:20:47.664639+00:00
-- url     : https://prove2.me/submissions/ed366720-1aa3-4d03-884f-b6df734622a5

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
    (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool) : dOp ε E cp * dOp ε E cp = 0 := by
  have hsum : dOp ε E cp =
      ∑ p ∈ plusIdx ε ×ˢ minusIdx ε, E p.2 p.1 * cp p.1 p.2 := by
    simp only [dOp, Finset.sum_product]
  rw [hsum]
  apply car_sum_sq_zero_of_anti
  intro x hx y hy
  simp only [Finset.mem_product, mem_plusIdx_iff_eq_true, mem_minusIdx_iff_eq_false] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have n1 : x.1 ≠ y.2 := fun h => by simp [h, hy2] at hx1
  have n2 : y.1 ≠ x.2 := fun h => by simp [h, hx2] at hy1
  have hAB : E x.2 x.1 * E y.2 y.1 = E y.2 y.1 * E x.2 x.1 := by
    have h := hE x.2 x.1 y.2 y.1
    rw [if_neg n1, if_neg n2, sub_zero] at h
    exact sub_eq_zero.mp h
  exact car_anti_abs _ _ _ _ ((hEC y.2 y.1 x.1 x.2).1).symm ((hEC x.2 x.1 y.1 y.2).1).symm hAB
    (eq_neg_iff_add_eq_zero.mpr (hC x.1 x.2 y.1 y.2).1)
end ReciprocityTheory.ChartRestriction.DS
