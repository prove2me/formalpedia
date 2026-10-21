-- Prove2me | solution 1 for PrepoLocal.Threshold.proposition_2b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T05:47:59.823307+00:00
-- url     : https://prove2.me/submissions/d210a16e-4f73-486e-b327-e7c8ee021bd0

import Mathlib
import Definitions.Def_PrepoLocal_Threshold_Model
import Theorems.Thm_PrepoLocal_Threshold_Ca_le_C
import Theorems.Thm_PrepoLocal_Threshold_eq_4_auxiliary_solution
import Theorems.Thm_PrepoLocal_Threshold_reduction_to_auxiliary
open MeasureTheory ProbabilityTheory
open PrepoLocal.Threshold

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : Params) (hP : P.Standing) (E : Env Ω) (hE : E.Standing μ)
    (xplus : ℝ) (hx : IsNetFractile μ E (betaStar P μ E) xplus)
    (M Tlo : ℝ) (hM : ∀ᵐ ω ∂μ, P.al * min (E.D ω) (E.Q ω) - E.R ω ≤ M)
    (hT : ∀ᵐ ω ∂μ, Tlo ≤ E.T ω)
    (hb : M - P.gam * Tlo + max xplus 0 ≤ P.b) :
    IsMinOn (C P μ E) (Set.Icc 0 P.b) (min (max xplus 0) P.b) ∧
      IsMinOn (Ca P μ E) (Set.Icc 0 P.b) (min (max xplus 0) P.b) ∧
      (0 ≤ M - P.gam * Tlo → min (max xplus 0) P.b = max xplus 0) := by
  have h4 := eq_4_auxiliary_solution μ P hP E hE xplus hx
  have hred := reduction_to_auxiliary μ P hP E hE xplus hx M Tlo hM hT hb
  refine ⟨?_, h4, fun h => min_eq_left (by linarith)⟩
  intro y hy
  have ha0 : 0 ≤ min (max xplus 0) P.b := le_min (le_max_right _ _) hP.2.2.2.2.1
  show C P μ E (min (max xplus 0) P.b) ≤ C P μ E y
  rw [hred _ ⟨ha0, le_rfl⟩]
  exact (h4 hy).trans (Ca_le_C μ P hP E hE y)
