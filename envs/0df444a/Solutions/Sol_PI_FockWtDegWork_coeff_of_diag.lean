-- Prove2me | solution 1 for PI.FockWtDegWork.coeff_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:40:24.210424+00:00
-- url     : https://prove2.me/submissions/31358a9b-54d4-44d6-a029-68f0ef6053b3

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockWeightDegree_ExistsMonomialWeight

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
open PI PI.FockWtDegWork
namespace PI.FockWtDegWork
theorem _root_.solution {σ : Type*} (T : Module.End ℂ (MvPolynomial σ ℂ)) (f : (σ →₀ ℕ) → ℂ)
    (hT : ∀ β, T (MvPolynomial.monomial β 1) = f β • MvPolynomial.monomial β 1)
    (P : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    MvPolynomial.coeff α (T P) = f α * MvPolynomial.coeff α P := by
  classical
  induction P using MvPolynomial.induction_on'
  next u a =>
    have hm : MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, hT]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, smul_eq_mul]
    split_ifs with h
    · subst h
      ring
    · simp
  next P Q hP hQ =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hP, hQ, mul_add]
end PI.FockWtDegWork
