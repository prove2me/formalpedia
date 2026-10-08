-- Prove2me | solution 1 for TroppMatrixConcentration.ch3_probabilistic_lieb
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:22:00.980243+00:00
-- url     : https://prove2.me/submissions/c8b7fd6a-97fa-41c9-bac2-06d3a31abe49

import Theorems.Thm_TroppMatrixConcentration_lieb_concavity
import Theorems.Thm_TroppMatrixConcentration_ch3_lieb_jensen
import Theorems.Thm_TroppMatrixConcentration_ch3_cgf_exp_log
import Theorems.Thm_TroppMatrixConcentration_ch3_lieb_integral_posDef
import Theorems.Thm_TroppMatrixConcentration_ch3_lieb_regularity_shift_integrable
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace TroppMatrixConcentration

lemma ch3_lieb_traceLog_continuousOn {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) :
    ContinuousOn (fun A => traceExp (H + matrixLog A))
      {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef} := by
  let : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hl : ContinuousOn (matrixLog : Matrix (Fin d) (Fin d) ℂ → _)
      {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef} :=
    CFC.continuousOn_log.mono (fun A hA => ⟨hA.isHermitian, hA.isUnit⟩)
  have he : ContinuousOn (fun A => matrixExp (H + matrixLog A))
      {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef} :=
    NormedSpace.exp_continuous.comp_continuousOn (continuousOn_const.add hl)
  exact Complex.continuous_re.comp_continuousOn
    ((Matrix.traceLinearMap (Fin d) ℂ ℂ).toContinuousLinearMap.continuous.comp_continuousOn he)

end TroppMatrixConcentration

open TroppMatrixConcentration

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
    (X : Ω → Matrix (Fin d) (Fin d) ℂ)
    (hMeas : Measurable X) (hHerm : ∀ᵐ ω ∂μ, (X ω).IsHermitian)
    (hExp : Integrable (fun ω => matrixExp (X ω)) μ) :
    (∫ ω, traceExp (H + X ω) ∂μ) ≤
      traceExp (H + matrixLog (∫ ω, matrixExp (X ω) ∂μ)) := by
  have hp : ∀ᵐ ω ∂μ, (matrixExp (X ω)).PosDef :=
    hHerm.mono fun ω hω => (ch3_cgf_exp_log (X ω) hω).1
  have hm := ch3_lieb_integral_posDef μ (fun ω => matrixExp (X ω)) hExp hp
  have heq : (fun ω => traceExp (H + matrixLog (matrixExp (X ω)))) =ᵐ[μ]
      (fun ω => traceExp (H + X ω)) :=
    hHerm.mono fun ω hω => by dsimp only; rw [(ch3_cgf_exp_log (X ω) hω).2]
  have hi := (ch3_lieb_regularity_shift_integrable μ H hH X hMeas hHerm hExp).2
  rw [← integral_congr_ae heq]
  exact ch3_lieb_jensen μ _ _ _ (lieb_concavity H hH)
    (ch3_lieb_traceLog_continuousOn H) hp hExp (hi.congr heq.symm) hm
