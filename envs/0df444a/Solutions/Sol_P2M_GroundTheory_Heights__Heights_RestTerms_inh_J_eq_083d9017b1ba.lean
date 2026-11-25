-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_inh_J_eq_083d9017b1ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:33.414121+00:00
-- url     : https://prove2.me/submissions/4c1ed9de-fed4-4c03-af41-110f6a20e51d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_mu_eq_f35e2c531be1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_fib_eq_3eb15ec2cff6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_inh_van_eq_517663f47d01

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution : fibreDegree 1 1 1 .last = -1 := by
  have hH : smallBlockMu 1 1 1 .last ^ (1 * (1 * 1)) * fibreClass 1 1 1 .last = flagTwoSecondRoot := by
    simp [inh_mu_eq, inh_fib_eq]
  rw [fibreDegree, hH, flagIntegral, inh_van_eq]
  have hne : ((0:Fin 1), (0 : Fin (1+1))) ≠ ((0:Fin 1), (1 : Fin (1+1))) := by decide
  rw [Finset.sum_eq_single (Finsupp.single ((0:Fin 1), (1 : Fin (1+1))) 1)]
  · simp [flagTwoFirstRoot, flagTwoSecondRoot, coeff_X', Finsupp.single_left_inj, hne, hne.symm, Finsupp.single_eq_single_iff]
  · intro b _ hb
    have : coeff b flagTwoSecondRoot = 0 := by
      rw [coeff_X']; exact if_neg (fun h => hb h.symm)
    simp [this]
  · intro h
    have : coeff (Finsupp.single ((0:Fin 1), (1 : Fin (1+1))) 1) (flagTwoFirstRoot - flagTwoSecondRoot) = 0 := by
      simpa using h
    simp [flagTwoFirstRoot, flagTwoSecondRoot, coeff_X', Finsupp.single_eq_single_iff, hne, hne.symm] at this
end GroundTheory.Heights₂.Heights.RestTerms
