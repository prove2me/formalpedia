-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P20.testingDivergence_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:28:02.198428+00:00
-- url     : https://prove2.me/submissions/270325e5-e15c-4825-8242-4526af0d9971

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

noncomputable section

open Filter

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

namespace X7M2TD

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem X7_oneEffect : IsBinaryEffect (1 : H →L[ℂ] H) := by
  have hadj : ContinuousLinearMap.adjoint (1 : H →L[ℂ] H) = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  refine ⟨⟨hadj, fun x => ?_⟩, ⟨by simp, fun x => by simp⟩⟩
  have : (inner ℂ x ((1 : H →L[ℂ] H) x)).re = ‖x‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  rw [this]; positivity

theorem X7_accept_one {I : Type*} (b : HilbertBasis I ℂ H) (rho : State b) :
    traceAcceptance b 1 rho.val.val = 1 := by
  simpa only [traceAcceptance, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp, Complex.one_re] using congrArg Complex.re rho.property.2

theorem X7_beta_le_one {I : Type*} (b : HilbertBasis I ℂ H) (rho sigma : State b)
    (epsilon : ℝ) (hZero : 0 ≤ epsilon) :
    hilbertTestingBeta b epsilon rho.val.val sigma.val.val ≤ 1 := by
  unfold hilbertTestingBeta
  apply sInf_le
  refine ⟨⟨1, X7_oneEffect⟩, ?_, ?_⟩
  · simp only [X7_accept_one b rho]; linarith
  · simp only [X7_accept_one b sigma, ENNReal.ofReal_one]

end X7M2TD

end QAlgorithms.Papers.Independent.Support50.P20

end

noncomputable section

open Filter

open scoped ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open QAlgorithms.Papers.Independent.Support50.P20 QAlgorithms.Papers.Independent.Support50.P20.X7M2TD in
theorem solution {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : State b) (epsilon : ℝ) (hZero : 0 ≤ epsilon) (hOne : epsilon < 1) :
    0 ≤ hilbertTestingDivergence b epsilon rho.val.val sigma.val.val ∧
    (rho = sigma → epsilon = 0 →
      hilbertTestingDivergence b epsilon rho.val.val sigma.val.val = 0) := by
  have hle := X7_beta_le_one b rho sigma epsilon hZero
  constructor
  · unfold hilbertTestingDivergence negativeLogTwo
    split_ifs with h0 htop
    · exact le_top
    · exact absurd (htop ▸ hle) (by simp)
    · have hpos : 0 < (hilbertTestingBeta b epsilon rho.val.val sigma.val.val).toReal :=
        ENNReal.toReal_pos h0 htop
      have hle1 : (hilbertTestingBeta b epsilon rho.val.val sigma.val.val).toReal ≤ 1 := by
        have := ENNReal.toReal_mono ENNReal.one_ne_top hle
        simpa using this
      have : logTwo (hilbertTestingBeta b epsilon rho.val.val sigma.val.val).toReal ≤ 0 := by
        unfold logTwo
        exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hpos.le hle1)
          (Real.log_nonneg (by norm_num))
      exact_mod_cast (show (0:ℝ) ≤ -logTwo _ by linarith)
  · rintro rfl rfl
    have hge : 1 ≤ hilbertTestingBeta b 0 rho.val.val rho.val.val := by
      unfold hilbertTestingBeta
      apply le_sInf
      rintro z ⟨Q, hQ, rfl⟩
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have h1 : hilbertTestingBeta b 0 rho.val.val rho.val.val = 1 := le_antisymm hle hge
    unfold hilbertTestingDivergence
    rw [h1]
    simp [negativeLogTwo, logTwo]
