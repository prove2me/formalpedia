-- Prove2me | solution 1 for SuReturns.Coordination.eq32_33_contract_margins
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:13:07.686814+00:00
-- url     : https://prove2.me/submissions/c48bdf2d-5967-4500-832b-8ba51cf1606a

import Mathlib
import Definitions.Def_SuReturns_Coordination_Model

open MeasureTheory ProbabilityTheory

theorem SuReturns.Coordination.eq32_33_contract_margins (ν : Measure ℝ) (c s φ w b l : ℝ)
    (hw : w = φ * c + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hb : b = φ * s + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hl : b - l = s) :
    w - b = φ * (c - s) ∧
      SuReturns.PartialRefunds.reservationPrice ν (b - l) - b = φ * (SuReturns.PartialRefunds.reservationPrice ν s - s) := by
  rw [hl, hw, hb]
  constructor <;> ring

theorem solution (ν : Measure ℝ) (c s φ w b l : ℝ)
    (hw : w = φ * c + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hb : b = φ * s + (1 - φ) * SuReturns.PartialRefunds.reservationPrice ν s)
    (hl : b - l = s) :
    w - b = φ * (c - s) ∧
      SuReturns.PartialRefunds.reservationPrice ν (b - l) - b = φ * (SuReturns.PartialRefunds.reservationPrice ν s - s) := SuReturns.Coordination.eq32_33_contract_margins ν c s φ w b l hw hb hl

#print axioms solution
