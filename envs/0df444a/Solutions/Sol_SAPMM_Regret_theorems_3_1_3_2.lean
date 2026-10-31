-- Prove2me | solution 1 for SAPMM.Regret.theorems_3_1_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:42:18.913992+00:00
-- url     : https://prove2.me/submissions/9894a9d8-d587-45ff-90e6-9cefa7993b77

import Mathlib
import Definitions.Def_SAPMM_Regret_Model
import Theorems.Thm_SAPMM_Regret_theorem_3_1
import Theorems.Thm_SAPMM_Regret_theorem_3_2

open MeasureTheory ProbabilityTheory
open SAPMM.Regret

theorem solution {n p : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : ℕ → Ω → Ξ) (hξ : IsIIDSample μ ξ)
    (P : Problem n p Ξ) (hP : P.Standing) (hPE : P.FiniteExpect (μ.map (ξ 0)))
    (hS : P.Slater (μ.map (ξ 0))) (T : ℕ) (hT : 1 ≤ T)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ P.X0)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (lam : ℕ → Ω → EuclideanSpace ℝ (Fin p))
    (hrun : IsRun P (1 / Real.sqrt T) (Real.sqrt T) x0 ξ x lam)
    (hTp : 2 * (p : ℝ) * P.κg ^ 2 < 3 * (T : ℝ)) :
    (∀ i, ∫ ω, ∑ t ∈ Finset.range T, P.G (x t ω) (ξ t ω) i ∂μ ≤ P.κc * Real.sqrt T) ∧
    (∀ xs ∈ P.Phi (μ.map (ξ 0)),
      ∫ ω, ∑ t ∈ Finset.range T, P.F (x t ω) (ξ t ω) ∂μ ≤
        ∫ ω, ∑ t ∈ Finset.range T, P.F xs (ξ t ω) ∂μ + P.κo * Real.sqrt T) :=
  ⟨SAPMM.Regret.theorem_3_1 μ ξ hξ P hP hPE hS T hT hx0 x lam hrun hTp,
    SAPMM.Regret.theorem_3_2 μ ξ hξ P hP hPE T hT hx0 x lam hrun⟩
