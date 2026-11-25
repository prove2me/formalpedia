-- Prove2me | solution 1 for PI.FHS.fockInner_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:39.644926+00:00
-- url     : https://prove2.me/submissions/f77bd3fb-2b3a-42ce-bb9a-08c23f9e3dae

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_fockInner_eq_sum_left
import Theorems.Thm_PI_FHS_fockInner_add_left
import Theorems.Thm_PI_FHS_fockInner_add_right
import Theorems.Thm_PI_FHS_fockInner_zero_right
import Theorems.Thm_PI_FHS_wt_add_single
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial
namespace PI.FHS
variable {σ : Type*}
private theorem X_mul_monomial_eq_monomial_add_single (l : σ) (a : σ →₀ ℕ) (c : ℂ) :
    X l * monomial a c = monomial (a + Finsupp.single l 1) c := by
  rw [add_comm]
  rw [MvPolynomial.monomial_single_add, pow_one]
private theorem fockInner_monomial_monomial_self (a : σ →₀ ℕ) (c d : ℂ) :
    FockH1Action.fockInner (monomial a c) (monomial a d) = (starRingEnd ℂ) c * d * wt a := by
  classical
  rw [fockInner_eq_sum_left _ _ {a} support_monomial_subset, Finset.sum_singleton]
  simp [coeff_monomial]
private theorem fockInner_monomial_monomial_of_ne (a b : σ →₀ ℕ) (c d : ℂ) (h : b ≠ a) :
    FockH1Action.fockInner (monomial a c) (monomial b d) = 0 := by
  classical
  rw [fockInner_eq_sum_left _ _ {a} support_monomial_subset, Finset.sum_singleton]
  simp [coeff_monomial, h]
end PI.FHS
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution [Fintype σ] (l : σ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (X l * P) Q = FockH1Action.fockInner P (pderiv l Q) := by
  classical
  refine MvPolynomial.induction_on' P (fun a c => ?_) (fun P P' hP hP' => ?_)
  · refine MvPolynomial.induction_on' Q (fun b d => ?_) (fun Q Q' hQ hQ' => ?_)
    · rw [X_mul_monomial_eq_monomial_add_single, pderiv_monomial]
      by_cases h : b = a + Finsupp.single l 1
      · subst h
        rw [add_tsub_cancel_right, fockInner_monomial_monomial_self, fockInner_monomial_monomial_self,
          wt_add_single, Finsupp.add_apply, Finsupp.single_eq_same]
        push_cast
        ring
      · rw [fockInner_monomial_monomial_of_ne _ _ _ _ h]
        by_cases hbl : b l = 0
        · rw [hbl, Nat.cast_zero, mul_zero, map_zero, fockInner_zero_right]
        · have hb : b - Finsupp.single l 1 + Finsupp.single l 1 = b := by
            ext i
            by_cases hi : i = l
            · subst hi
              simp
              omega
            · simp [Ne.symm hi]
          have hne : b - Finsupp.single l 1 ≠ a := fun he => h (hb.symm.trans (by rw [he]))
          rw [fockInner_monomial_monomial_of_ne _ _ _ _ hne]
    · rw [fockInner_add_right, map_add, fockInner_add_right, hQ, hQ']
  · rw [mul_add, fockInner_add_left, fockInner_add_left, hP, hP']
end PI.FHS
