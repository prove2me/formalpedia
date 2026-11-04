-- Prove2me | solution 1 for PerishBaseStock.Lifo.eq_27
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:03:46.336676+00:00
-- url     : https://prove2.me/submissions/fa7ab8a4-c3b5-4ad1-946e-db37971f9ce9

import Definitions.Def_PerishBaseStock_Lifo_Heuristic
import Theorems.Thm_PerishBaseStock_Lifo_lemma_3
import Theorems.Thm_PerishBaseStock_Lifo_proposition_2

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic
open PerishBaseStock.Lifo

theorem solution (P : CappedBaseStock.DemandLaw) (c : Params) (hc : c.Standing)
    (Sh St : ℝ≥0) (hSh : IsHatMinimizer P c Sh) (hSt : IsTildeMinimizer P c St) :
    baseStockCost P c Sh ≤ OPT P c + ENNReal.ofReal (c.θ / (2 * c.m) *
      (expectedHolding P.law Sh + expectedHolding P.law St
        - expectedHolding (maxLaw P (c.m - 1)) Sh + expectedHolding (maxLaw P (c.m - 1)) St
        - 2 * expectedHolding (leadTimeLaw P (c.m - 1)) St)) := by
  have hU := (lemma_3 P c hc Sh).2
  have hO := proposition_2 P c hc St hSt
  have hmin := hSh St
  have key : hatCU P c Sh ≤ tildeC P c St + c.θ / (2 * c.m) *
      (expectedHolding P.law Sh + expectedHolding P.law St
        - expectedHolding (maxLaw P (c.m - 1)) Sh + expectedHolding (maxLaw P (c.m - 1)) St
        - 2 * expectedHolding (leadTimeLaw P (c.m - 1)) St) := by
    unfold hatObjective hatCL hatCU at hmin
    unfold hatCU tildeC backorderCost
    unfold backorderCost at hmin
    have h2 : c.θ / (2 * c.m) = c.θ / c.m / 2 := by rw [div_div, mul_comm (c.m : ℝ) 2]
    rw [h2]
    linear_combination hmin
  refine hU.trans ?_
  refine (ENNReal.ofReal_le_ofReal key).trans ?_
  refine (ENNReal.ofReal_add_le).trans ?_
  exact add_le_add hO le_rfl
