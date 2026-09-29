-- Prove2me | solution 1 for VeinottBaseStock.base_stock_level_absorbing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:35:47.303374+00:00
-- url     : https://prove2.me/submissions/ed3e2c57-6815-4ed2-a470-6209a1358eea

import Mathlib
import Definitions.Def_VeinottBaseStock_Model
import Definitions.Def_VeinottBaseStock_BaseStock

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

theorem aux_bsla_state_congr {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) :
    ∀ k (d d' : ℕ → Fin m → ℝ), (∀ j, j < k → d j = d' j) →
      M.baseStockState ybar x₁ d k = M.baseStockState ybar x₁ d' k := by
  intro k
  induction k with
  | zero => intro d d' _; rfl
  | succ k ih =>
    intro d d' h
    simp only [Model.baseStockState]
    rw [ih d d' (fun j hj => h j (Nat.lt_succ_of_lt hj)), h k (Nat.lt_succ_self k)]

theorem aux_bsla_extend {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) (d : ℕ → Fin m → ℝ) (k : ℕ) :
    M.baseStockState ybar x₁ (extendHist (fun j : Fin k => d j)) k
      = M.baseStockState ybar x₁ d k := by
  apply aux_bsla_state_congr
  intro j hj
  simp [extendHist, hj]

theorem aux_bsla_order {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) (d : ℕ → Fin m → ℝ) (k : ℕ) :
    M.orderSeq (M.baseStock ybar x₁) d k
      = M.baseStockRule ybar k (M.baseStockState ybar x₁ d k) := by
  simp only [Model.orderSeq, Model.baseStock]
  rw [aux_bsla_extend]

theorem aux_bsla_stateSeq {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) (d : ℕ → Fin m → ℝ) :
    ∀ k, M.stateSeq (M.baseStock ybar x₁) x₁ d k = M.baseStockState ybar x₁ d k := by
  intro k
  cases k with
  | zero => rfl
  | succ k =>
    simp only [Model.stateSeq, Model.baseStockState]
    rw [aux_bsla_order]

end VeinottBaseStock

open VeinottBaseStock
open MeasureTheory ProbabilityTheory

theorem solution {n m : ℕ} (M : Model n m) (ybar : ℕ → Fin n → ℝ)
    (x₁ : Fin n → ℝ) (hM : M.Standing) (hx₁ : x₁ ∈ M.X 0) (h3b : M.H3b ybar)
    (d : ℕ → Fin m → ℝ) (hd : ∀ j, d j ∈ M.Dset j) (k : ℕ)
    (hk : M.q k (M.stateSeq (M.baseStock ybar x₁) x₁ d k) ≤ coeVec (ybar k)) :
    ∀ i, k ≤ i → M.orderSeq (M.baseStock ybar x₁) d i = ybar i := by
  rw [aux_bsla_stateSeq] at hk
  have key : ∀ i, k ≤ i → M.q i (M.baseStockState ybar x₁ d i) ≤ coeVec (ybar i) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact hk
    | succ i _ ih =>
      simp only [Model.baseStockState, Model.baseStockRule, if_pos ih]
      exact h3b i (d i) (hd i)
  intro i hi
  rw [aux_bsla_order]
  simp only [Model.baseStockRule, if_pos (key i hi)]
