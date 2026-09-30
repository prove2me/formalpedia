-- Prove2me | solution 1 for SupplyChainTheory.buyback_profit_identities
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:58:55.447217+00:00
-- url     : https://prove2.me/submissions/581bdeaf-ea07-4b71-a10f-f51288626ae2

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

lemma sc_int_min (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (Q : ℝ) : Integrable (fun d => min Q d) D := by
  refine Integrable.mono' ((integrable_const |Q|).add hD.abs)
    (measurable_const.min measurable_id).aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rcases le_total Q d with h | h
  · rw [min_eq_left h]; linarith [abs_nonneg d]
  · rw [min_eq_right h]; linarith [abs_nonneg Q]

lemma sc_leftover (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (Q : ℝ) : expLeftover D Q = Q - expSales D Q := by
  unfold expLeftover expSales
  have h : ∀ d, max (Q - d) 0 = Q - min Q d := by
    intro d
    rcases le_total Q d with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]
  simp_rw [h]
  rw [integral_sub (integrable_const Q) (sc_int_min D hD Q), integral_const]
  simp

lemma sc_rv (P : ContractData) : 0 < P.r - P.v := by
  have := P.profitable; have := P.cs_nonneg; have := P.v_lt_cr; linarith

lemma sc_K (P : ContractData) : 0 < P.r - P.v + P.p := by
  have := sc_rv P; have := P.ps_nonneg; have := P.pr_nonneg
  simp only [ContractData.p]; linarith

lemma sc_bb_ident (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (b Q : ℝ) :
    retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q
        = buybackShare P b * chainProfit P D Q
          + meanDemand D * (buybackShare P b * P.p - P.pr)
      ∧ supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q
        = (1 - buybackShare P b) * chainProfit P D Q
          - meanDemand D * (buybackShare P b * P.p - P.pr) := by
  have hK := (sc_K P).ne'
  unfold retailerProfit supplierProfit buybackTransfer buybackPrice buybackShare chainProfit
  rw [sc_leftover D hD Q]
  simp only [ContractData.c, ContractData.p] at hK ⊢
  constructor <;> field_simp <;> ring

end SupplyChainTheory

open SupplyChainTheory

theorem solution (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (b Q : ℝ) :
    retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q
        = buybackShare P b * chainProfit P D Q
          + meanDemand D * (buybackShare P b * P.p - P.pr)
      ∧ supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q
        = (1 - buybackShare P b) * chainProfit P D Q
          - meanDemand D * (buybackShare P b * P.p - P.pr) := by
  exact sc_bb_ident P D hD b Q
