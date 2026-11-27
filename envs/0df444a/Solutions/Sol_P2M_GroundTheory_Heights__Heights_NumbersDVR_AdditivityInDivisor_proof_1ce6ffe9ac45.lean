-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_proof_1ce6ffe9ac45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:05:46.939557+00:00
-- url     : https://prove2.me/submissions/573e138e-f587-4753-9d34-ebc600f68945

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtOfAddOneLe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_cycle_ad3e7e5b4611
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_cycEval_add_fn_45f3c9bda240
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_support_finite_137b8be27f7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_withBot_lt_of_add_one_le_ca3eb079d909
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_ratDiv_mul_mul_0239d507d543
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
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace AdditivityInDivisor
theorem _root_.solution (hmul : DivCycleMul.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u})
    (hadd : IntNumAddFirst.Statement.{u}) (hsup : SupSpanMultiHomog.Statement.{u})
    (hmin : MinimalPrimeMultiHomog.Statement.{u}) (hspm : SpecialIdealMultiHomog.Statement.{u})
    (hcor : SpecialIdealCorresp.Statement.{u}) (hqd : SpecialQuotDim.Statement.{u})
    (hdrop : DimStrictDrop.Statement.{u}) : AdditivityInDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b₁ b₂ f₁ g₁ f₂ g₂ hD₁ hD₂ c s hs hsP hsH L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have rfin : ∀ (Q : Ideal (MRing ι O)) (x y : MRing ι O), (Function.support (ratDiv Q x y)).Finite :=
    fun Q x y => ratDiv_support_finite (hfin O K ι Q x) (hfin O K ι Q y)
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [ratDiv_mul_mul hmul hPp hD₁.num_not_mem hD₂.num_not_mem hD₁.den_not_mem hD₂.den_not_mem]
    exact cycEval_add_cycle (rfin _ _ _) (rfin _ _ _)
  · unfold cutIdentityRightSide
    refine cycEval_add_fn (hfin O K ι P s) fun W hW => ?_
    obtain ⟨hWp, hPW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
    split_ifs with hϖW
    ·
      have hWmin : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
        unfold divCycle at hW
        split_ifs at hW with h
        · exact h.1
        · exact absurd rfl hW
      have hWh : IsMultiHomogIdeal W :=
        hmin O K ι _ W (hsup O K ι P s c hP.multiProj.multiHomog hs) hWmin
      have hsW : s ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
      have hlt : P < W := lt_of_le_of_ne hPW fun h => hsP (h ▸ hsW)
      have hdim := hdrop (MRing ι O) P W hlt
      rw [hP.dim, ← hqd O ϖ hϖ K ι W hϖW,
        show d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K by ring] at hdim
      exact hadd _ K ι d (specialIdeal W) (hcor O ϖ hϖ K ι P W hWp hϖW).1 (hspm O K ι W hWh)
        (withBot_lt_of_add_one_le hdim) b₁ b₂ L
    ·
      obtain ⟨hV₁, hV₂⟩ := hsH W hW hϖW
      rw [ratDiv_mul_mul hmul hWp hV₁.num_not_mem hV₂.num_not_mem hV₁.den_not_mem hV₂.den_not_mem]
      exact cycEval_add_cycle (rfin _ _ _) (rfin _ _ _)
end AdditivityInDivisor
end GroundTheory.Heights₂.Heights.NumbersDVR
