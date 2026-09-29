-- Prove2me | solution 1 for PreorderADI.Correlation.second_profit_deriv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:38:23.395298+00:00
-- url     : https://prove2.me/submissions/eb112605-853f-4e99-897c-a79f4737bc8e

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem aux_spd_pdf_pos (x : ℝ) : 0 < stdNormalPdf x := by
  unfold stdNormalPdf
  exact gaussianPDFReal_pos 0 1 x one_ne_zero

end PreorderADI.Correlation

open PreorderADI.Correlation
open MeasureTheory ProbabilityTheory

theorem solution (P : Params) (hP : P.Standing)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun r => secondProfit P r 0)
      (P.vL * stdNormalPdf P.zL * P.sigmaL * (ρ / Real.sqrt (1 - ρ ^ 2))) ρ ∧
    0 < P.vL * stdNormalPdf P.zL * P.sigmaL * (ρ / Real.sqrt (1 - ρ ^ 2)) := by
  obtain ⟨h0, h1⟩ := hρ
  have hpos : 0 < 1 - ρ ^ 2 := by nlinarith
  have hsq : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos.mpr hpos
  refine ⟨?_, ?_⟩
  · have hin : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (0 - (2:ℕ) * ρ ^ (2 - 1)) ρ :=
      (hasDerivAt_const ρ (1:ℝ)).sub (hasDerivAt_pow 2 ρ)
    have hs := hin.sqrt hpos.ne'
    have hc : HasDerivAt (fun r : ℝ => (P.vL - P.c) * (P.muL + r * P.sigmaL * 0)) 0 ρ := by
      have : (fun r : ℝ => (P.vL - P.c) * (P.muL + r * P.sigmaL * 0)) =
          fun _ => (P.vL - P.c) * P.muL := by
        funext r; ring
      rw [this]; exact hasDerivAt_const ρ _
    have hall := hc.sub (hs.const_mul (P.vL * stdNormalPdf P.zL * P.sigmaL))
    have hfun : (fun r => secondProfit P r 0) =
        ((fun r : ℝ => (P.vL - P.c) * (P.muL + r * P.sigmaL * 0)) -
          fun y => P.vL * stdNormalPdf P.zL * P.sigmaL * √(1 - y ^ 2)) := by
      funext r; rfl
    rw [hfun]
    refine hall.congr_deriv ?_
    push_cast
    field_simp
    ring
  · have := aux_spd_pdf_pos P.zL
    have hvL : 0 < P.vL := lt_trans hP.c_pos hP.c_lt_vL
    have := hP.sigmaL_pos
    positivity
