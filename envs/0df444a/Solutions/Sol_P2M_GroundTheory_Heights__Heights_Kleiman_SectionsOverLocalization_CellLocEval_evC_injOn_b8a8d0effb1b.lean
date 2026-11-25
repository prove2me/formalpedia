-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_evC_injOn_b8a8d0effb1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:24:52.575536+00:00
-- url     : https://prove2.me/submissions/06c8c7f4-4736-458c-b8ce-814cbabfb3fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDMemLocPart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_evMap_injOn_a970953ea151
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_subsingleton_of_not_258815edc3e8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc cechZc cechBc cechHc
  mIdealOver quotPart)
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
variable (γ : K → ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
theorem _root_.solution (n : ℕ) :
    Set.InjOn (evC (S := S) y n) (cechCc ι (quotPart S (mIdealOver S y)) γ n) := by
  intro w hw w' hw' h
  funext I
  have h' := congrFun h I
  rw [evC_apply, evC_apply] at h'
  by_cases hI : CellMeets y I.1
  · exact evMap_injOn y hI γ (Submodule.mem_pi.mp hw I (Set.mem_univ _))
      (Submodule.mem_pi.mp hw' I (Set.mem_univ _)) h'
  · have := subsingleton_of_not (S := S) y hI
    exact Subsingleton.elim _ _
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
