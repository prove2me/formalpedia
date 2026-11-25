-- Prove2me | solution 1 for PI.QnCovHatW.qnCovHat_of_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:42:02.323798+00:00
-- url     : https://prove2.me/submissions/8b5d02a2-ecf2-472a-9790-9b47563a590b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_InjDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_SkipOneEqSuccAbove
import Theorems.Thm_PI_QnCovHatW_qminor_skip
import Theorems.Thm_PI_QnCovHatW_int_smul_eq
import Theorems.Thm_PI_QnCovHatW_swap4
import Theorems.Thm_PI_QnCovHatW_det_sub_eq
import Theorems.Thm_P2M_PI_QnCovHatW_det_sub_eq__8094bc80bf43
import Theorems.Thm_PI_QnCovHatW_scal
import Theorems.Thm_Formalism_REAL_quantumMinorColSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinorRowSkew_holds
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_zero_of_col_eq
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_zero_of_row_eq
import Theorems.Thm_PI_QnCovHatW_alt_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix Formalism.REAL Formalism.FourierDecayAlt.Q
open PI PI.QnCovHatW
namespace PI.QnCovHatW
theorem _root_.solution (hL : PI.QnCovLin) : PI.QnCovHat := by
  intro A _ _ n E P Q hE hQP hPQ u a β
  cases n with
  | zero => simp [chatA]
  | succ m =>
  have rskew : ∀ (d c : Fin m → Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      qminor E (c ∘ σ) d u = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminor E c d u := by
    intro d c σ
    rw [int_smul_eq]
    exact quantumMinorRowSkew_holds A (m + 1) m E c d σ u
  have rzero : ∀ (d c : Fin m → Fin (m + 1)), ¬ Function.Injective c → qminor E c d u = 0 := by
    intro d c hc
    obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hc
    exact quantumMinor_eq_zero_of_row_eq quantumMinorRowSkew_holds E c d u p q hne hpq
  have cskew : ∀ (c d : Fin m → Fin (m + 1)) (σ : Equiv.Perm (Fin m)),
      qminor E c (d ∘ σ) u = ((Equiv.Perm.sign σ : ℤ) : ℂ) • qminor E c d u := by
    intro c d σ
    rw [int_smul_eq]
    exact quantumMinorColSkew_holds A (m + 1) m E hE c d σ u
  have czero : ∀ (c d : Fin m → Fin (m + 1)), ¬ Function.Injective d → qminor E c d u = 0 := by
    intro c d hd
    obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hd
    exact quantumMinor_eq_zero_of_col_eq quantumMinorColSkew_holds E hE c d u p q hne hpq
  have key : ∀ i j : Fin (m + 1), qminor (Econj E P Q) i.succAbove j.succAbove u =
      ∑ i' : Fin (m + 1), ∑ j' : Fin (m + 1),
        ((P.submatrix i'.succAbove i.succAbove).det * (Q.submatrix j.succAbove j'.succAbove).det) •
          qminor E i'.succAbove j'.succAbove u := by
    intro i j
    rw [hL A (m + 1) m E P Q hQP i.succAbove j.succAbove u]
    simp_rw [mul_smul]
    simp_rw [← Finset.smul_sum]
    have inner : ∀ c : Fin m → Fin (m + 1),
        ∑ d : Fin m → Fin (m + 1), (∏ k, Q (j.succAbove k) (d k)) • qminor E c d u =
          ∑ j' : Fin (m + 1), (Q.submatrix j.succAbove j'.succAbove).det • qminor E c j'.succAbove u := by
      intro c
      rw [alt_sum (fun d => qminor E c d u) (cskew c) (czero c)]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [det_sub_eq']
    simp_rw [inner]
    rw [alt_sum (fun c => ∑ j' : Fin (m + 1),
        (Q.submatrix j.succAbove j'.succAbove).det • qminor E c j'.succAbove u) ?_ ?_]
    · refine Finset.sum_congr rfl fun i' _ => ?_
      rw [det_sub_eq, Finset.smul_sum]
    · intro c σ
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [rskew, smul_comm]
    · intro c hc
      refine Finset.sum_eq_zero fun j' _ => ?_
      rw [rzero _ c hc, smul_zero]
  simp only [chatA, qminor_skip]
  simp_rw [key, Finset.smul_sum, smul_smul]
  rw [swap4]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ => ?_
  simp_rw [← Finset.sum_smul]
  rw [scal P Q hPQ a β i' j']
end PI.QnCovHatW
