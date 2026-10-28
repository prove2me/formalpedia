-- Prove2me | solution 1 for SLPEPricing.Regret.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:22:20.776026+00:00
-- url     : https://prove2.me/submissions/5c7a95be-2f8d-496c-bb39-617ec8cedd8f

import Mathlib
import Definitions.Def_SLPEPricing_Regret_Model

open SLPEPricing.Regret

theorem solution (d : ℝ → ℝ) (pstar κ : ℝ) (hd : Differentiable ℝ d)
    (hpos : 0 < pstar) (hlt : pstar < 1)
    (hmax : ∀ p ∈ Set.Icc (0 : ℝ) 1, r d p ≤ r d pstar)
    (hκ : 0 < κ)
    (hA1 : ∀ p ∈ Set.Icc (0 : ℝ) 1, d pstar - κ * (p - pstar) ^ 2 ≤ -(deriv d p) * pstar) :
    ∀ p ∈ Set.Icc (0 : ℝ) 1, pstar * (deriv d p - deriv d pstar) ≤ κ * (p - pstar) ^ 2 := by
  intro p hp
  have hloc : IsLocalMax (r d) pstar := by
    refine Filter.mem_of_superset (Icc_mem_nhds hpos hlt) ?_
    intro x hx
    exact hmax x hx
  have hder : HasDerivAt (r d) (1 * d pstar + pstar * deriv d pstar) pstar :=
    (hasDerivAt_id pstar).mul (hd pstar).hasDerivAt
  have h0 := hloc.hasDerivAt_eq_zero hder
  have h := hA1 p hp
  nlinarith
