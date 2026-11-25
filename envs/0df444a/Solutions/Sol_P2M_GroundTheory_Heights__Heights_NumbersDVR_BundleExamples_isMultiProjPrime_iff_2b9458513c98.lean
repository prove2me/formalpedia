-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isMultiProjPrime_iff_2b9458513c98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:32.555925+00:00
-- url     : https://prove2.me/submissions/8a300a52-d33b-4371-aa3d-1f05915bfad8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomogIdeal_proof_6afd59a7e16a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_VocabMultiHomog_proof_8751c6dffe37


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
set_option linter.unusedSectionVars false
universe u
variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
theorem _root_.solution (P : Ideal (MRing ι O)) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P ↔ IsMultiProjPrime P := by
  have hI := VocabMultiHomogIdeal.proof VocabMultiHomog.proof O K ι P
  constructor
  · rintro ⟨hp, hh, hr⟩
    exact ⟨hp, hI.1 hh, hr⟩
  · rintro ⟨hp, hh, hr⟩
    exact ⟨hp, hI.2 hh, hr⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
