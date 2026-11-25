-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_map_evMap_locPart_347e12ef343f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:12.243816+00:00
-- url     : https://prove2.me/submissions/038cf713-4f66-491b-bf0a-152ca79206a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_evMap_mk_175d3062bc25
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_rep_9868982c704f

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
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc mIdealOver mConeMapOver
  quotPart)
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
theorem _root_.solution {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) (γ : K → ℤ) :
    (locPart ι (quotPart S (mIdealOver S y)) (cellMon S I) γ).map (evMap y I) = cellSec S y γ I := by
  unfold cellSec
  rw [if_pos hI]
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro x hx
    obtain ⟨g, t, a, ht, hg, hd, rfl⟩ := exists_rep hx
    rw [Submodule.mem_comap, evMap_mk y hI]
    rcases hd with hd | rfl
    · exact Submodule.subset_span ⟨g, t, a, t.2, ht, hd, hg, rfl⟩
    · rw [map_zero, zero_div]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro z ⟨g, t, a, ht, ht', hnn, hg, rfl⟩
    refine ⟨LocalizedModule.mk (Ideal.Quotient.mk _ g) ⟨t, ht⟩,
      Submodule.subset_span ⟨Ideal.Quotient.mk _ g, ⟨t, ht⟩, a, ht', ?_, rfl⟩, evMap_mk y hI g ⟨t, ht⟩⟩
    exact Submodule.subset_span ⟨g, ⟨hnn, hg⟩, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
