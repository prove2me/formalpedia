-- Prove2me | solution 1 for TradeCreditIns.Cancelable.upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:00:23.884976+00:00
-- url     : https://prove2.me/submissions/e88410f5-1a75-415e-b150-81e9152116a6

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model

open TradeCreditIns.Cancelable

theorem solution (P : Params) (hS : P.Standing) :
    ∀ κ : Contract, κ.IsCancelable P →
      InsurerMonitors P κ → supplierPayoff P κ ≤ firstBest P := by
  intro κ _ hM
  obtain ⟨hθ, -, -, hβ0, h01, h12, -, -, -, hl, -⟩ := hS
  have hL : ∀ x, 0 ≤ L P x := fun x => mul_nonneg hl (le_max_right _ _)
  have hβ : ∀ i, 0 ≤ P.β i := by
    intro i; fin_cases i <;> simp <;> linarith
  classical
  let s : Fin 3 → Bool := fun i =>
    if Cancels P κ (P.β i) then decide (ShipsUncovered P κ (P.β i))
    else decide (ShipsCovered P κ (P.β i))
  have hterm : ∀ i : Fin 3,
      P.θ i *
        (if Cancels P κ (P.β i) then
           κ.f + (if ShipsUncovered P κ (P.β i) then
             (1 - P.β i) * P.r - P.β i * L P (κ.f - κ.p) else P.r0)
         else if ShipsCovered P κ (P.β i) then
           P.r - P.β i * (κ.δ + L P (P.r - κ.δ - κ.p))
         else P.r0)
      - P.θ i *
        (if Cancels P κ (P.β i) then κ.f
         else if ShipsCovered P κ (P.β i) then P.β i * (P.r - κ.δ) else 0)
      ≤ P.θ i * (if s i then (1 - P.β i) * P.r else P.r0) := by
    intro i
    rw [← mul_sub]
    apply mul_le_mul_of_nonneg_left _ (hθ i)
    have h1 := hL (κ.f - κ.p)
    have h2 := hL (P.r - κ.δ - κ.p)
    have hb := hβ i
    by_cases hc : Cancels P κ (P.β i)
    · by_cases hu : ShipsUncovered P κ (P.β i)
      · simp only [s, hc, hu, if_true, decide_true]
        nlinarith [mul_nonneg hb h1]
      · simp only [s, hc, hu, if_true, if_false, decide_false]
        simp
    · by_cases hv : ShipsCovered P κ (P.β i)
      · simp only [s, hc, hv, if_true, if_false, decide_true]
        nlinarith [mul_nonneg hb h2]
      · simp only [s, hc, hv, if_false, decide_false]
        simp
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  rw [Finset.sum_sub_distrib] at hsum
  have hp := hM.2.2
  unfold insurerCostEffort at hp
  have key : supplierPayoff P κ ≤
      (∑ i, P.θ i * (if s i then (1 - P.β i) * P.r else P.r0)) - P.c := by
    unfold supplierPayoff
    linarith
  unfold firstBest
  refine le_trans key (le_trans ?_ (le_max_right _ _))
  exact Finset.le_sup' (fun s : Fin 3 → Bool =>
        (∑ i, P.θ i * (if s i then (1 - P.β i) * P.r else P.r0)) - P.c)
    (Finset.mem_univ s)
