-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionDivProof_eq_of_lt_of_le_of_mem_minimalPrimes_a75b2d9b45b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:06:47.938743+00:00
-- url     : https://prove2.me/submissions/50ce81fd-7d3e-463d-a3be-d09830e9053a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMultAtOfSaturated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionDiv

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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionDivProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionDivProof
theorem _root_.solution {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [P.IsPrime] [Q.IsPrime] {x : A}
    (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P < Q) (hQW : Q ≤ W) : Q = W := by
  by_contra hne
  have hQW' : Q < W := lt_of_le_of_ne hQW hne
  have : W.IsPrime := hW.1.1
  let f := Ideal.Quotient.mk P
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hPW : P ≤ W := hPQ.le.trans hQW
  have hker : RingHom.ker f = P := Ideal.mk_ker
  have : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hPW)
  have : (Q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hPQ.le)
  have h1 : (W.map f).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hlt : Q.map f < W.map f := by
    refine (Ideal.map_mono hQW).lt_of_not_ge fun e => hQW'.not_ge ?_
    have := Ideal.comap_mono (f := f) e
    rwa [Ideal.comap_map_of_surjective f hf, Ideal.comap_map_of_surjective f hf,
      ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPW, sup_eq_left.mpr hPQ.le] at this
  have : (W.map f).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have h2 := (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt).trans_le h1
  rw [Order.lt_one_iff, Ideal.height_eq_zero_iff_eq_bot] at h2
  refine hPQ.not_ge fun q hq => ?_
  have h3 : f q ∈ Q.map f := Ideal.mem_map_of_mem f hq
  rw [h2, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h3
  exact h3
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleSectionDivProof
