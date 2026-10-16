-- Prove2me | solution 1 for PooledRationing.AsymFeas.claim_22
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T07:55:00.90282+00:00
-- url     : https://prove2.me/submissions/42e0c65a-45fa-4005-b979-ff3534bad130

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting

set_option autoImplicit false
open PooledRationing.AsymFeas MeasureTheory

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Jiang, Wang and Zhang, SSRN 3385089, equations (21)–(22).
theorem solution {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (ε : ℝ) (_hε : 0 < ε) (lam : RandPolicy P c)
    (h21 : ∀ w : Fin n → ℝ, 0 ≤ w → (∑ j, w j) ≤ 1 →
      ∑ j, w j * (β j - service F R lam j) ≤ ε) :
    ∀ j, β j - ε ≤ service F R lam j := by
  classical
  intro j
  have hn : (0 : Fin n → ℝ) ≤ Pi.single j 1 := by
    intro i
    by_cases he : i = j <;> simp [he]
  have hs : (∑ i : Fin n, Pi.single j (1 : ℝ) i) ≤ 1 := by simp
  have h := h21 (Pi.single j 1) hn hs
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  linarith
