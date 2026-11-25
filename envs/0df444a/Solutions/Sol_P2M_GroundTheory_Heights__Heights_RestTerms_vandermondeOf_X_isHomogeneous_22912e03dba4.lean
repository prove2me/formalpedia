-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_isHomogeneous_22912e03dba4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:41.276892+00:00
-- url     : https://prove2.me/submissions/9dcfaa61-5e9e-4b37-a2cd-94f6248e7a79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFrobeniusCharacterFormula
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sub_e9512e82a813


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (r : ℕ) :
    (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ))).IsHomogeneous
      (r * (r - 1) / 2) := by
  have h := IsHomogeneous.prod (σ := Fin r) (R := ℚ) Finset.univ
    (fun i : Fin r => ∏ j ∈ Finset.Ioi i, ((X i : MvPolynomial (Fin r) ℚ) - X j))
    (fun i => ∑ _j ∈ Finset.Ioi i, 1)
    (fun i _ => IsHomogeneous.prod _ _ _ fun j _ =>
      (isHomogeneous_X ℚ i).sub (isHomogeneous_X ℚ j))
  have hdeg : ∑ i : Fin r, ∑ _j ∈ Finset.Ioi i, (1 : ℕ) = r * (r - 1) / 2 := by
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Ioi]
    rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, ← Finset.sum_range_id]
    exact Finset.sum_range_reflect (fun i => i) r
  rw [hdeg] at h
  exact h
end GroundTheory.Heights₂.Heights.RestTerms
