-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isModelOver_iff_72f2abf14dfc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:10:57.204503+00:00
-- url     : https://prove2.me/submissions/fdb4be11-7c16-4954-bf3e-a10b857f1df0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isMultiProjPrime_iff_2b9458513c98

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
theorem _root_.solution (P : Ideal (MRing ι O)) (d : ℕ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d ↔ Nonempty K ∧ IsModelOver P d := by
  rw [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver, isMultiProjPrime_iff]
  constructor
  · rintro ⟨hK, hP, ht, hd⟩
    exact ⟨hK, hP, ht, hd⟩
  · rintro ⟨hK, hP, ht, hd⟩
    exact ⟨hK, hP, ht, hd⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
