-- Prove2me | solution 1 for SmoothAmbEq.Gaussian.theorem_5_5_equilibrium
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T20:43:16.142253+00:00
-- url     : https://prove2.me/submissions/4c974f61-ba7b-4ace-bd51-941802bac3db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SmoothAmbEq_Gaussian_Model
import Definitions.Def_SmoothAmbEq_Gaussian_InsideSystem
import Definitions.Def_SmoothAmbEq_Gaussian_Equilibrium
import Definitions.Def_SmoothAmbEq_Gaussian_Candidate
import Theorems.Thm_SmoothAmbEq_Gaussian_pi_star_admissible
import Theorems.Thm_SmoothAmbEq_Gaussian_theorem_5_5_equilibrium_condition

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

open SmoothAmbEq.Gaussian

theorem solution (M : Model) (a : ℝ) (ha : IsAlphaStar M a)
    (hα : max a (1 - 1 / 2 * (M.σ ^ 2 / (M.σ₀ ^ 2 * M.T))) < M.α) (c : Coeffs)
    (hc : SolvesODE510 M c) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P) :
    IsEquilibrium M P W (piStar M c) :=
  ⟨pi_star_admissible M a ha hα c hc P W hW,
    theorem_5_5_equilibrium_condition M a ha hα c hc P W hW⟩
