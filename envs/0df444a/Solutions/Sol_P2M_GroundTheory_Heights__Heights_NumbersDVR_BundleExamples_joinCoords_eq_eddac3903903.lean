-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_joinCoords_eq_eddac3903903
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:01.977804+00:00
-- url     : https://prove2.me/submissions/f2faf281-e3aa-44df-ba86-c00ce425d3c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm

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
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
theorem _root_.solution {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) :
    joinCoords y y' = IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y y' := by
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples
