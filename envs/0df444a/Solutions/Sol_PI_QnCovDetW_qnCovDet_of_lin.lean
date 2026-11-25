-- Prove2me | solution 1 for PI.QnCovDetW.qnCovDet_of_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:18.037269+00:00
-- url     : https://prove2.me/submissions/9087517f-cd54-4ddb-906a-41ee9193d0d5

import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantDeterminantScaling_IntCastMulEqSmul
import Theorems.Thm_PI_QnCovDetW_sum_fun_eq_sum_perm
import Theorems.Thm_PI_QnCovDetW_qminor_perm_perm
import Theorems.Thm_PI_QnCovDetW_sum_sign_prod_left
import Theorems.Thm_PI_QnCovDetW_sum_sign_prod_right
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinorRowSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_zero_of_col_eq
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_zero_of_row_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnCovDetW
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovDetW
theorem _root_.solution (h : PI.QnCovLin) : PI.QnCovDet := by
  intro A _ _ n E P Q hE hQP hPQ u
  have hrep : ∀ c : Fin n → Fin n, ¬ Function.Injective c → ∃ p q, p ≠ q ∧ c p = c q := by
    intro c hc
    by_contra hne
    push_neg at hne
    exact hc (fun p q hpq => by_contra fun h => hne p q h hpq)
  have hrow : ∀ c d : Fin n → Fin n, ¬ Function.Injective c → qminor E c d u = 0 := by
    intro c d hc
    obtain ⟨p, q, hpq, hcq⟩ := hrep c hc
    exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hpq hcq
  have hcol : ∀ c d : Fin n → Fin n, ¬ Function.Injective d → qminor E c d u = 0 := by
    intro c d hd
    obtain ⟨p, q, hpq, hdq⟩ := hrep d hd
    exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d u p q hpq hdq
  have key : qdet (Econj E P Q) u = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      ((((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, P (σ k) k) * (((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ k, Q k (τ k))) • qdet E u := by
    rw [show qdet (Econj E P Q) u = qminor (Econj E P Q) id id u from rfl, h A n n E P Q hQP id id u,
      sum_fun_eq_sum_perm]
    · refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [sum_fun_eq_sum_perm]
      · refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [qminor_perm_perm E hE σ τ u, smul_smul]
        congr 1
        try simp only [id_eq]
        ring
      · intro d hd
        rw [hcol _ d hd, smul_zero]
    · intro c hc
      exact Finset.sum_eq_zero (fun d _ => by rw [hrow c d hc, smul_zero])
  rw [key]
  simp_rw [← Finset.sum_smul]
  rw [← Finset.sum_mul_sum, sum_sign_prod_left, sum_sign_prod_right, ← Matrix.det_mul, hPQ,
    Matrix.det_one, one_smul]
end PI.QnCovDetW
