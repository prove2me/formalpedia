-- Prove2me | solution 1 for ShortWDRODual.Legendre.theorem_1_soft
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:00:07.031264+00:00
-- url     : https://prove2.me/submissions/c4ead409-6393-41af-9224-27c98b7f4370

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting
import Theorems.Thm_ShortWDRODual_Legendre_legendre_eq_softValue
import Theorems.Thm_ShortWDRODual_Legendre_softValue_eq_couplingSup

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.Legendre

theorem solution {X : Type*} [MeasurableSpace X]
    (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (c : X → X → ENNReal)
    (hf : Measurable f)
    (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (hc : Measurable (fun p : X × X => c p.1 p.2))
    (hc0 : ∀ x, c x x = 0)
    (lam : ℝ) (hlam : 0 < lam) :
    legendre (fun ρ => - robustLoss c f Phat ρ) (-lam) =
      ⨆ γ ∈ couplingsFst Phat, extIntegral γ (phiLam c f lam) := by
  rw [legendre_eq_softValue Phat f c hf hfint hc hc0 lam hlam,
    softValue_eq_couplingSup Phat f c hf hfint hc hc0 lam hlam.le]
