-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_eval_top_e1c72c19af4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:48:53.500346+00:00
-- url     : https://prove2.me/submissions/c8e8962e-1e1e-43fc-ab28-43963c0dec1d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvAtTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvPolynomialReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvMonomialReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStepReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvIdealRepresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCoinvStaircaseDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StaircaseIsHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagProportional_staircase_isHomogeneous_713be1057cf7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvAtTop_proof_7264ddd9e7c0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvIdealComponent_proof_f098e93102bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvIdealRepresentation_proof_04cfae8b11db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvMonomialReduction_proof_77102dd9ef11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvPolynomialReduction_proof_3ff9742bbded
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvStaircaseComponent_proof_f0c640dde185
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvStaircaseDegree_proof_96f3a35ebb69
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_CoinvStepReduction_proof_a8ba17646d54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sub_e9512e82a813
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HomogeneousComponentMul_proof_071fefd82e0b


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
open GroundTheory.Heights₂.Heights.RestTerms.FlagProportional
namespace GroundTheory.Heights₂.Heights.RestTerms.FlagProportional
theorem _root_.solution (f j k : ℕ) (L : IndefiniteRowSideFullHecke.RestTerms.Roots f j k →ₗ[ℝ] ℝ)
    (hL : ∀ (m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k), 1 ≤ m →
      m ≤ IndefiniteRowSideFullHecke.RestTerms.dimFl f j k → G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k - m) →
        L (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0)
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (hG : G.IsHomogeneous (IndefiniteRowSideFullHecke.RestTerms.dimFl f j k)) (c : ℝ)
    (hc : G - C c * monomial (Coinv.staircase f (j + k)) 1 ∈ Coinv.psumIdeal ℝ f (j + k)) :
    L G = c * L (monomial (Coinv.staircase f (j + k)) 1) := by
  classical
  set D := IndefiniteRowSideFullHecke.RestTerms.dimFl f j k
  set s : IndefiniteRowSideFullHecke.RestTerms.Roots f j k := monomial (Coinv.staircase f (j + k)) 1
  obtain ⟨Q, hQ, hEq⟩ := CoinvIdealComponent.proof CoinvIdealRepresentation.proof
    HomogeneousComponentMul.proof ℝ f (j + k) _ hc D
  have hJ : (G - C c * s).IsHomogeneous D := hG.sub ((staircase_isHomogeneous f j k).C_mul c)
  have hcomp : homogeneousComponent D (G - C c * s) = G - C c * s := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hJ), if_pos rfl]
  have e1 := hcomp.symm.trans hEq
  have e2 : G - C c * s = homogeneousComponent D
      (∑ m ∈ Finset.Icc 1 (j + k), ∑ b : Fin f, Coinv.bps ℝ f (j + k) m b * Q m b) := by
    rw [← e1, hcomp]
  have hzero : L (G - C c * s) = 0 := by
    rw [e2, map_sum, map_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hp : (Coinv.bps ℝ f (j + k) m b).IsHomogeneous m :=
      IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr (hp.mul (hQ m b)))]
    split_ifs with h
    · exact hL m b (Q m b) hm1 (by omega) (hQ m b)
    · exact map_zero L
  calc L G = L (G - C c * s) + L (C c * s) := by rw [← map_add, sub_add_cancel]
    _ = c * L s := by rw [hzero, zero_add, C_mul', map_smul, smul_eq_mul]
end GroundTheory.Heights₂.Heights.RestTerms.FlagProportional
