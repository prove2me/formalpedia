-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ratDiv_mul_655de8ec8838
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:27:15.582364+00:00
-- url     : https://prove2.me/submissions/f0c32507-f159-4909-beee-5e7bf89e9478

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
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimStrictDrop_proof_15777780f510
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialIdealCorresp_proof_bd738eb41ba7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialIdealMultiHomog_proof_41306882bd1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialQuotDim_proof_5536281ab8d6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VerticalDivisorsCommute_proof_79421367f623


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
universe u
variable {K : Type} [DecidableEq K] {ι : K → Type}
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [Fintype K] [∀ k, Fintype (ι k)]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι O)} [P.IsPrime] {f g f' g' : MRing ι O} (hf : f ∉ P)
    (hg : g ∉ P) (hf' : f' ∉ P) (hg' : g' ∉ P) :
    ratDiv P (f * f') (g * g') = ratDiv P f g + ratDiv P f' g' := by
  funext W
  simp only [ratDiv, Pi.add_apply]
  rw [DivCycleMul.proof O K ι P f f' ‹_› hf hf', DivCycleMul.proof O K ι P g g' ‹_› hg hg']
  simp only [Pi.add_apply]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR
