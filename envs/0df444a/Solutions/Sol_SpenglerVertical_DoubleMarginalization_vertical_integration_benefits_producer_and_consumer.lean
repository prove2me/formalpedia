-- Prove2me | solution 1 for SpenglerVertical.DoubleMarginalization.vertical_integration_benefits_producer_and_consumer
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:45:41.609105+00:00
-- url     : https://prove2.me/submissions/52ebb0b6-9947-47c5-9708-f44e73771add

import Theorems.Thm_SpenglerVertical_DoubleMarginalization_price_rises_with_cost

set_option autoImplicit false
open SpenglerVertical.DoubleMarginalization

theorem solution
    (D : ℝ → ℝ) (hD : Antitone D)
    (Va Vb Vc Pa Pb Pc Pc' : ℝ)
    (hRa : 0 < Pa - Va) (hRb : 0 < Pb - (Vb + Pa))
    (hPc : IsProfitMax D (Vc + Pb) Pc)
    (hPc' : IsProfitMax D (Va + Vb + Vc) Pc')
    (hdiff : DifferentiableAt ℝ D Pc) (hQ : 0 < D Pc) :
    Pc' < Pc ∧
    D Pc < D Pc' ∧
    (Pa - Va) * D Pc + (Pb - (Vb + Pa)) * D Pc + (Pc - (Vc + Pb)) * D Pc
      < (Pc' - (Va + Vb + Vc)) * D Pc' ∧
    D Pc * (Pc - Pc') ≤ ∫ x in Pc'..Pc, D x ∧
    0 < ∫ x in Pc'..Pc, D x := by
  have hcost : Va + Vb + Vc < Vc + Pb := by linarith
  have hcompare := price_rises_with_cost D (Va + Vb + Vc) (Vc + Pb) Pc' Pc hcost hPc' hPc
  have hp : Pc' < Pc := hcompare.2.2 hD hQ hdiff
  have hquant : D Pc < D Pc' := by
    apply lt_of_le_of_ne hcompare.1
    intro heq
    have h := hPc' Pc
    unfold profit at h
    rw [← heq] at h
    nlinarith
  have hprofit : profit D (Va + Vb + Vc) Pc < profit D (Va + Vb + Vc) Pc' := by
    apply lt_of_le_of_ne (hPc' Pc)
    intro heq
    have hnew : IsProfitMax D (Va + Vb + Vc) Pc := by
      intro x
      exact (hPc' x).trans (le_of_eq heq.symm)
    have hbad := (price_rises_with_cost D (Va + Vb + Vc) (Vc + Pb) Pc Pc hcost hnew hPc).2.2 hD hQ hdiff
    exact (lt_irrefl Pc) hbad
  have hint : D Pc * (Pc - Pc') ≤ ∫ x in Pc'..Pc, D x := by
    have h : (∫ x in Pc'..Pc, D Pc) ≤ ∫ x in Pc'..Pc, D x :=
      intervalIntegral.integral_mono_on (le_of_lt hp) intervalIntegrable_const
        hD.intervalIntegrable (fun x hx => hD hx.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  refine ⟨hp, hquant, ?_, hint, ?_⟩
  · unfold profit at hprofit
    nlinarith only [hprofit]
  · have hpos : 0 < D Pc * (Pc - Pc') := mul_pos hQ (sub_pos.mpr hp)
    linarith
