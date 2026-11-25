-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_proof_b3053cf7626b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:10:50.678368+00:00
-- url     : https://prove2.me/submissions/9c25890f-d300-4309-b8e1-56b88176f10e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairBundleTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_isMultiProjPrime_pointIdeal_058978c6cf77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_exists_ne_zero_of_span_5f8e06e12f5c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensSpan_proof_984f8b2ec229


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GenericProjClosureDim
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace GenericProjClosureDim
theorem _root_.solution (hDim : DvrConeDimTrdeg.Statement) (hTr : PairBundleTrdeg.Statement) :
    GenericProjClosureDim.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N hN E _ _ B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht

  have hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hli := ht.linearIndependent

  have hz : ∀ o, ∃ i, pairProjCoord y e φ φ' t ⟨o, i⟩ ≠ 0 := by
    rintro (_ | _ | k)
    · exact exists_ne_zero_of_span hN e hli φ'
        (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc)
    · exact exists_ne_zero_of_span hN e hli φ
        (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc)
    · exact ⟨c k, fun h0 => hc k ((FaithfulSMul.algebraMap_injective Ω Φ) (by simpa [pairProjCoord, projCoord] using h0))⟩
  have hP := isMultiProjPrime_pointIdeal (R := O) _ hz

  have hnt : (pointIdeal O (pairProjCoord y e φ φ' t)).comap (C : O →+* _) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply,
      C_eq_zero, IsScalarTower.algebraMap_apply O Ω Φ, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective Ω Φ)] at ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy
  refine ⟨hP, hnt, ?_⟩

  have hdy := hDim O K ι (pointIdeal O y) hV.multiProj hV.noTorsion
  rw [hV.dim] at hdy
  have hty : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = ((d + Fintype.card K : ℕ) : Cardinal) := by
    have h1 : (((d + Fintype.card K : ℕ) : ℕ∞) + 1) =
        (Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y)).toENat + 1 := by
      have := WithBot.coe_injective hdy
      rw [← this]
      push_cast
      ring
    exact (Cardinal.toENat_eq_natCast.1 (WithTop.add_right_cancel ENat.one_ne_top h1).symm)
  rw [hDim _ _ _ _ hP hnt, hTr O ϖ hϖ Ω K ι y d hV N hN E B B' hB M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht, hty,
    ← Nat.cast_add, Cardinal.toENat_nat, Fintype.card_option, Fintype.card_option,
    show d + (N - 1) + 1 + (Fintype.card K + 1 + 1) = d + Fintype.card K + (N + 1) + 1 by omega]
  norm_cast
end GenericProjClosureDim
end GroundTheory.Heights₂.Heights.NumbersDVR
