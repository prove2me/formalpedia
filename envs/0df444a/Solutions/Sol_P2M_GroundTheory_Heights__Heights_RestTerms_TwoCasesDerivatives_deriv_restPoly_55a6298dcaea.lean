-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_deriv_restPoly_55a6298dcaea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:12:32.634158+00:00
-- url     : https://prove2.me/submissions/4249907b-0b11-4c27-a762-6e7d049d72d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_SumPderivRealApply
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_prod_eq_zero_f8221cfdebfa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_derivation_vandermondeOf_eq_zero_e325c8c3d5fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_eq_vandermonde_144b4b56a0c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.TwoCasesDerivatives
open MvPolynomial Finset
noncomputable section
variable (f j k : ℕ)
namespace GroundTheory.Heights₂.Heights.RestTerms.TwoCasesDerivatives
theorem _root_.solution (D : Derivation ℝ (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (IndefiniteRowSideFullHecke.RestTerms.Roots f j k))
    (bot : Bool) (α β : Fin f → ℝ)
    (ht : ∀ σ (a : Fin j), D (X (σ, Fin.castAdd k a)) = C (α σ))
    (hb : ∀ σ (b : Fin k), D (X (σ, Fin.natAdd j b)) = C (β σ)) :
    D (IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot) =
      C (((IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1) *
          (if bot then (k : ℝ) * ∑ σ, β σ else -((j : ℝ) * ∑ σ, α σ))) *
        IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot := by
  have hfib : D (IndefiniteRowSideFullHecke.RestTerms.fibClass f j k bot) = 0 := by
    unfold IndefiniteRowSideFullHecke.RestTerms.fibClass
    refine Flag.derivation_prod_eq_zero D _ _ (fun σ _ => ?_)
    cases bot <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      rw [Derivation.leibniz, ← vandermondeOf_eq_vandermonde, ← vandermondeOf_eq_vandermonde,
        Flag.derivation_vandermondeOf_eq_zero D _ (fun i i' => by simp [ht, hb]),
        Flag.derivation_vandermondeOf_eq_zero D _ (fun i i' => by simp [ht, hb]),
        smul_zero, smul_zero, add_zero]
  have hmu : D (IndefiniteRowSideFullHecke.RestTerms.muClass f j k bot) =
      C (if bot then (k : ℝ) * ∑ σ, β σ else -((j : ℝ) * ∑ σ, α σ)) := by
    cases bot <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.muClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, map_sum, ht, hb, Finset.mul_sum]
  rw [IndefiniteRowSideFullHecke.RestTerms.restPoly, Derivation.leibniz, hfib, smul_zero, zero_add,
    Derivation.leibniz_pow, hmu, IndefiniteRowSideFullHecke.RestTerms.degPoly]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  simp only [map_mul, map_natCast, map_add, map_one]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.RestTerms.TwoCasesDerivatives
