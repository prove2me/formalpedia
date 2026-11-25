-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeIntegralMass_of_slices_7e0cd20a7e70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:45.055215+00:00
-- url     : https://prove2.me/submissions/c2e01468-5997-47cd-912e-e39157218b7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionDegreeSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPointSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFromLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace ConeIntegralMass
theorem _root_.solution (hCP : ConeToProjective.Statement)
    (hS : SliceSectionMass.Statement) (hA : SectionHyperplaneAvoid.Statement)
    (hD : SectionDegreeSum.Statement) (hP : PointSliceMass.Statement) :
    ConeIntegralMass.Statement := by
  intro n e
  induction e with
  | zero =>
    intro δ h W f hW hf hδ
    obtain ⟨j, hj⟩ := hW.isRelevant
    have hℓ : linForm (Pi.single j (1 : ℂ)) ∉ W := by rwa [linForm_single]
    rw [hCP n 0 h W f (Pi.single j 1) (fun _ => 1) hW hf hℓ (fun _ _ _ => rfl) continuousOn_const]
    exact hP n δ h W f _ hW hf hδ hℓ
  | succ e ih =>
    intro δ h J f hJ hf hδ
    obtain ⟨j, hj⟩ := hJ.isRelevant
    have hu : linForm (Pi.single j (1 : ℂ)) ∉ J := by rwa [linForm_single]
    obtain ⟨ℓ, hℓ, hℓW⟩ := hA n J (Pi.single j 1) hJ
    obtain ⟨g, δW, hW, hsum⟩ := hD ℂ n e δ J f (Pi.single j 1) hJ hf hδ hu
    rw [hCP n (e + 1) h J f ℓ (fun _ => 1) hJ hf hℓ (fun _ _ _ => rfl) continuousOn_const,
      hS n e h J f (Pi.single j 1) ℓ hJ hf hu hℓ hℓW, hsum]
    push_cast
    refine Finset.sum_congr rfl fun W hWm => ?_
    obtain ⟨hWp, hWc, hWδ⟩ := hW W hWm
    rw [← hCP n e h W (g W) ℓ (fun _ => 1) hWp hWc (hℓW W hWm) (fun _ _ _ => rfl)
      continuousOn_const, ih (δW W) h W (g W) hWp hWc hWδ]
end ConeIntegralMass
end GroundTheory.Heights₂.Heights
