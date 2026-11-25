-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_sameGenericFibre_trans_09b01538ecfc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:41.151214+00:00
-- url     : https://prove2.me/submissions/ac8cb51f-44fa-42c5-93f9-3d0df1af8e63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialQuotDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealCorresp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialIdealMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorsCommute
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairCocycle

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
  [Field Ω] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
  {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {τ : Type*} {x : τ → Ω} {ϖ : O} {B B' B'' : ChartBundle O x N E}
    (h₁ : SameGenericFibre ϖ B B') (h₂ : SameGenericFibre ϖ B' B'') : SameGenericFibre ϖ B B'' := by
  intro c hc
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨n, hn⟩ := (h₁ c hc).1 v hv
    obtain ⟨m, hm⟩ := (h₂ c hc).1 _ hn
    exact ⟨m + n, by rw [pow_add, mul_smul]; exact hm⟩
  · obtain ⟨n, hn⟩ := (h₂ c hc).2 v hv
    obtain ⟨m, hm⟩ := (h₁ c hc).2 _ hn
    exact ⟨m + n, by rw [pow_add, mul_smul]; exact hm⟩
end GroundTheory.Heights₂.Heights.NumbersDVR
