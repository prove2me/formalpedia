-- Prove2me | solution 1 for RiskPremiaDMP.Equivalence.artificial_productivity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:16:33.12901+00:00
-- url     : https://prove2.me/submissions/586b8fa4-3d9c-42de-bbc6-cd38ec3ae04d

import Mathlib
import Definitions.Def_RiskPremiaDMP_Equivalence_Model

open RiskPremiaDMP.Equivalence in
theorem solution (P : RPParams) (hP : P.Standing) (y η BQ Bη : ℝ → ℝ)
    (hy : Continuous y) (hη : Continuous η)
    (h15 : SolvesRiskNeutralY P y η BQ) (h12 : SolvesMPR P η Bη) :
    SolvesProductivity (artificial P) (fun t => toYQ P (y t)) (fun t => toMuQ P (η t))
      BQ (fun t => -Bη t) := by
  have hk : P.κy ≠ 0 := hP.1.ne'
  constructor
  · intro t ht
    have h := h15 t ht
    show toYQ P (y t) = toYQ P (y 0) +
      (∫ u in (0 : ℝ)..t, P.κy * (toMuQ P (η u) - toYQ P (y u))) + P.σy * (BQ t - BQ 0)
    have hint : (∫ u in (0 : ℝ)..t, P.κy * (toMuQ P (η u) - toYQ P (y u))) =
        ∫ u in (0 : ℝ)..t, P.κy * (-(P.σy / P.κy) * η u - y u) := by
      congr 1; funext u
      unfold toMuQ toYQ shift
      field_simp; ring
    rw [hint]
    unfold toYQ
    linarith
  · intro t ht
    have h := h12 t ht
    show toMuQ P (η t) = toMuQ P (η 0) +
      (∫ u in (0 : ℝ)..t, -(P.κη * toMuQ P (η u))) + P.ση * P.σy / P.κy * (-Bη t - -Bη 0)
    have hint : (∫ u in (0 : ℝ)..t, -(P.κη * toMuQ P (η u))) =
        (-(P.σy / P.κy)) * ∫ u in (0 : ℝ)..t, P.κη * (P.ηbar - η u) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext u
      unfold toMuQ
      field_simp
    rw [hint]
    unfold toMuQ
    have e1 : P.σy * (P.ηbar - η t) / P.κy = P.σy * P.ηbar / P.κy - (P.σy / P.κy) * η t := by
      field_simp
    have e2 : P.σy * (P.ηbar - η 0) / P.κy = P.σy * P.ηbar / P.κy - (P.σy / P.κy) * η 0 := by
      field_simp
    rw [e1, e2, h]
    ring
