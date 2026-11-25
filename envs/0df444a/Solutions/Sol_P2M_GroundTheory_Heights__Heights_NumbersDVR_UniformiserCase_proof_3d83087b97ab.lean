-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_UniformiserCase_proof_3d83087b97ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:39.220819+00:00
-- url     : https://prove2.me/submissions/6d35191f-0a7b-4baf-b77d-e185fe49df1e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_divCycle_ne_zero_77d65d882a25
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_one_6db77f3f161a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_vNum_cons_zero_9549e2b329f7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_C_eq_bot_of_not_mem_1f5ac74ee822
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_le_of_add_one_le_a9caad75ac39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_withBot_lt_of_add_one_le_98f037542015
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_le_and_isRelevant_of_divCycle_ne_zero_6b368bc3dee6


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
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace UniformiserCase
theorem _root_.solution (h1 : ConservationOfNumberLE.Statement.{u})
    (h2 : GenericDimBound.Statement.{u}) (h3 : GenericFibProps.Statement.{u})
    (h4 : GenericCycleCorresp.Statement.{u}) (h5 : MinimalPrimeMultiHomog.Statement.{u})
    (h6 : SupSpanMultiHomog.Statement.{u}) (h7 : DimStrictDrop.Statement.{u})
    (h8 : CutByForm.Statement.{u}) : UniformiserCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP c s hs hsP L
  have hdim : ringKrullDim (MRing ι O ⧸ P) = ((d + 1 + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    hP.dim
  have := hP.multiProj.isPrime

  have hL : cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P (C ϖ) 1) =
      gNum P (Matrix.vecCons (fun k => (c k : ℤ)) L) := by
    rw [ratDiv_one]
    exact h1 O ϖ hϖ K ι P (d + 1) hP.multiProj hP.noTorsion hdim.le _

  obtain ⟨hGprime, hGhom, hGs⟩ := h3 O K ι P hP.multiProj hP.noTorsion
  obtain ⟨hsG, hsG'⟩ := hGs s c hs hsP
  have hGdim : ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) <
      ((d + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have e : d + 2 + Fintype.card K = (d + 1 + Fintype.card K) + 1 := by omega
    rw [e]
    refine withBot_lt_of_add_one_le _ _ ?_
    have := h2 O K ι P hP.multiProj hP.noTorsion
    rw [hdim] at this
    rwa [show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega] at this
  have hcut := h8 (FractionRing O) K ι d (genFib P) hGprime hGhom hGdim _ c hsG hsG' L
  have hcorr := h4 O ϖ hϖ K ι P s hP.multiProj.isPrime hP.noTorsion hsP
    (fun V => intNum (FractionRing O) V L)
  rw [cutIdentity, hL, gNum, hcut, ← hcorr]

  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : divCycle P s W = 0
  · rw [hW, zero_mul, zero_mul]
  congr 1
  dsimp only
  by_cases hϖW : (C ϖ : MRing ι O) ∈ W
  · rw [if_pos hϖW, if_pos hϖW, vNum_cons_zero]
  rw [if_neg hϖW, if_neg hϖW]
  obtain ⟨hWmin, hWrel⟩ := mem_minimalPrimes_of_divCycle_ne_zero hW
  obtain ⟨hWprime, hPW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  have := hWprime
  have hWhom : IsMultiHomogIdeal W :=
    h5 O K ι (P ⊔ Ideal.span {s}) W (h6 O K ι P s c hP.multiProj.multiHomog hs) hWmin
  have hlt : P < W := lt_of_le_of_ne hPW fun h => hsP (h ▸ hWmin.1.2
    (Ideal.mem_sup_right (Ideal.subset_span rfl)))
  have hWdim : ringKrullDim (MRing ι O ⧸ W) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    refine withBot_le_of_add_one_le _ _ ?_
    have := h7 (MRing ι O) P W hlt
    rw [hdim] at this
    rwa [show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by omega] at this
  rw [ratDiv_one]
  exact (h1 O ϖ hϖ K ι W d ⟨hWprime, hWhom, hWrel⟩ (comap_C_eq_bot_of_not_mem hϖ W hϖW) hWdim L).symm
end UniformiserCase
end GroundTheory.Heights₂.Heights.NumbersDVR
