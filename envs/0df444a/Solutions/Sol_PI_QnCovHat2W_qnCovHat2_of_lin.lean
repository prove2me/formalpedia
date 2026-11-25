-- Prove2me | solution 1 for PI.QnCovHat2W.qnCovHat2_of_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:26:20.2308+00:00
-- url     : https://prove2.me/submissions/134a7d57-ee89-45e0-be63-4a3b45d39e40

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SumSgnLProdCol
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_QnCovHat2OfLin
import Theorems.Thm_PI_QnCovHat2W_qminor_row_alt
import Theorems.Thm_PI_QnCovHat2W_qminor_col_alt
import Theorems.Thm_Formalism_QuantumDeterminants_glRelAd
import Theorems.Thm_PI_QnCovHat2W_GG_cov
import Theorems.Thm_PI_QnCovHat2W_GG_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution (hLin : PI.QnCovLin) : PI.QnCovHat2 := by
  intro A _ _ n E P Q hE hQP hPQ u a a' β β'
  rcases n with _ | _ | m
  · simp [chat2A]
  · simp [chat2A]
  · have hE' : GlRel (Econj E P Q) := glRelAd A (m + 2) E P Q hE hQP
    have h1 := GG_eq (fun x y : Fin m → Fin (m + 2) => qminor E x y u)
      (fun x y π => qminor_row_alt E u x y π) (fun x y π => qminor_col_alt E hE u x y π) β β' a a'
    have h2 := GG_eq (fun x y : Fin m → Fin (m + 2) => qminor (Econj E P Q) x y u)
      (fun x y π => qminor_row_alt (Econj E P Q) u x y π)
      (fun x y π => qminor_col_alt (Econj E P Q) hE' u x y π) (β ᵥ* P) (β' ᵥ* P) (Q *ᵥ a) (Q *ᵥ a')
    have h3 := GG_cov (fun x y : Fin m → Fin (m + 2) => qminor E x y u)
      (fun x y : Fin m → Fin (m + 2) => qminor (Econj E P Q) x y u) P Q
      (fun x y => hLin A (m + 2) m E P Q hQP x y u) β β' a a'
    have hdet : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
    rw [hdet, one_smul, h1, h2] at h3
    have hne : ((m.factorial : ℂ) * m.factorial) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
        (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
    have h4 := congrArg (fun z => ((m.factorial : ℂ) * m.factorial)⁻¹ • z) h3
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
    exact h4
end PI.QnCovHat2W
