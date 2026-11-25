-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_evC_lift_e8f11abc73fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:35:10.676737+00:00
-- url     : https://prove2.me/submissions/f2ada732-f09b-4da5-8af1-ed9291993678

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechDMemLocPart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_map_evMap_locPart_347e12ef343f


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
theorem _root_.solution (n : ℕ) {w' : Cell K ι n → Ω} (hw' : w' ∈ cellC S y γ n) :
    ∃ w ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n, evC y n w = w' := by
  have h : ∀ I : Cell K ι n, ∃ x ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) γ,
      evMap y I.1 x = w' I := by
    intro I
    have hI' : w' I ∈ cellSec S y γ I.1 := Submodule.mem_pi.mp hw' I (Set.mem_univ _)
    by_cases hI : CellMeets y I.1
    · rw [← map_evMap_locPart y hI γ] at hI'
      exact Submodule.mem_map.mp hI'
    · unfold cellSec at hI'
      rw [if_neg hI, Submodule.mem_bot] at hI'
      exact ⟨0, Submodule.zero_mem _, by rw [map_zero, hI']⟩
  choose w hw hφw using h
  exact ⟨w, Submodule.mem_pi.mpr fun I _ => hw I, funext hφw⟩
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
