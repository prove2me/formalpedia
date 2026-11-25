-- Prove2me | solution 1 for PI.FockOneDegW.Diag.coeff_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:40:13.56089+00:00
-- url     : https://prove2.me/submissions/99d61892-157c-490e-a72d-ed62158b28fa

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockOneDegW PI.FockOneDegW.Diag
namespace PI.FockOneDegW.Diag
theorem _root_.solution {σ : Type*} (T : Module.End ℂ (MvPolynomial σ ℂ)) (f : (σ →₀ ℕ) → ℂ)
    (hT : ∀ β, T (MvPolynomial.monomial β 1) = f β • MvPolynomial.monomial β 1)
    (P : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    MvPolynomial.coeff α (T P) = f α * MvPolynomial.coeff α P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hu : MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hu, map_smul, hT, smul_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul,
      MvPolynomial.coeff_monomial]
    by_cases h : u = α
    · subst h
      simp only [if_true, smul_eq_mul, mul_one]
      ring
    · simp only [h, if_false, smul_eq_mul, mul_zero]
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, h₁, h₂, mul_add]
end PI.FockOneDegW.Diag
