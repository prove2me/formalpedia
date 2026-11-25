-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isSec_iff_cc429de364eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:54.260935+00:00
-- url     : https://prove2.me/submissions/4e2a5c91-d070-4145-9182-6e87fe125eea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) :
    IsSec P A s ↔ ∃ a : K → ℕ, (∀ k, A.a k = a k) ∧ IsMultiHomog s a ∧ s ∉ P := by
  constructor
  · rintro ⟨a, hs, ha, hP⟩
    exact ⟨a, fun k => (ha k).symm, hs, hP⟩
  · rintro ⟨a, ha, hs, hP⟩
    exact ⟨a, hs, fun k => (ha k).symm, hP⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
