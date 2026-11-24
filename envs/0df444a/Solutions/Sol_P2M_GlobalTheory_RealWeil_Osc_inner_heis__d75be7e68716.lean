-- Prove2me | solution 1 for P2M_GlobalTheory_RealWeil_Osc_inner_heis__d75be7e68716
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:12:57.761154+00:00
-- url     : https://prove2.me/submissions/3f1ffde9-771d-4239-b1ae-c3dc17742cfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Theorems.Thm_GlobalTheory_RealWeil_Osc_heis_neg
import Theorems.Thm_GlobalTheory_RealWeil_Osc_inner_heis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Osc
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ ρ' : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false
variable {T : B →L[ℂ] B}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Φ : B →L[ℂ] H}
namespace GlobalTheory.RealWeil.Osc
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (hΦ : ∀ v f, ‖Φ (ρ v f)‖ = ‖Φ f‖) (v : V)
    (x y : B) : inner ℂ (Φ x) (Φ (ρ v y)) = inner ℂ (Φ (ρ (-v) x)) (Φ y) := by
  rw [← inner_heis hΦ v (ρ (-v) x), heis_neg hJ h]
end GlobalTheory.RealWeil.Osc
