-- Prove2me | solution 1 for ServiceParts.StockLevels.theta_max_zero_stock
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:27:56.440263+00:00
-- url     : https://prove2.me/submissions/049457bb-9c4a-4985-9545-02c4d1451795

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems



namespace ServiceParts.StockLevels

lemma tz_pmf0 (d : CompoundPoissonDemand) : d.pmf 0 = Real.exp (-(d.lam * d.tbar)) := by
  simp [CompoundPoissonDemand.pmf]

lemma tz_pmf0_pos (d : CompoundPoissonDemand) : 0 < d.pmf 0 := by
  rw [tz_pmf0]; exact Real.exp_pos _

lemma tz_pmf0_lt (d : CompoundPoissonDemand) : d.pmf 0 < 1 := by
  rw [tz_pmf0, Real.exp_lt_one_iff]
  have := mul_pos d.lam_pos d.tbar_pos
  linarith

lemma tz_ready0 (d : CompoundPoissonDemand) : d.readyRate 0 = d.pmf 0 := by
  simp [CompoundPoissonDemand.readyRate]

theorem theta_max_zero_stock_core {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    (∀ i, 0 < thetaZero (d i) (c i) ∧
      (d i).pmf 0 = 1 / (1 + thetaZero (d i) (c i) * c i)) ∧
    ∀ i, IsLeast
      (stockSet (d i) (c i) (Finset.univ.sup' Finset.univ_nonempty
        (fun j => thetaZero (d j) (c j)))) 0 := by
  have key : ∀ i, 0 < thetaZero (d i) (c i) ∧
      (d i).pmf 0 = 1 / (1 + thetaZero (d i) (c i) * c i) := by
    intro i
    have hp := tz_pmf0_pos (d i)
    have hp1 := tz_pmf0_lt (d i)
    have hci := hc i
    unfold thetaZero
    constructor
    · apply mul_pos (by positivity)
      rw [sub_pos, lt_one_div (by norm_num) hp]; simpa using hp1
    · field_simp; ring
  refine ⟨key, fun i => ⟨?_, fun _ _ => Nat.zero_le _⟩⟩
  show 1 / (1 + _ * c i) ≤ (d i).readyRate 0
  rw [tz_ready0, (key i).2]
  have hle : thetaZero (d i) (c i) ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun j => thetaZero (d j) (c j)) :=
    Finset.le_sup' (f := fun j => thetaZero (d j) (c j)) (Finset.mem_univ i)
  have h0 := (key i).1
  have hci := hc i
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

end ServiceParts.StockLevels

open ServiceParts.StockLevels


theorem solution {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (hc : ∀ i, 0 < c i) :
    (∀ i, 0 < thetaZero (d i) (c i) ∧
      (d i).pmf 0 = 1 / (1 + thetaZero (d i) (c i) * c i)) ∧
    ∀ i, IsLeast
      (stockSet (d i) (c i) (Finset.univ.sup' Finset.univ_nonempty
        (fun j => thetaZero (d j) (c j)))) 0 := by
  exact theta_max_zero_stock_core d c hc
