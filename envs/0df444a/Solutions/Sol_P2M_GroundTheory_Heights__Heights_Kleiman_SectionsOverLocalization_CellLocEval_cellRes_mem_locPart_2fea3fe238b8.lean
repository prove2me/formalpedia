-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_cellRes_mem_locPart_2fea3fe238b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:44:35.635803+00:00
-- url     : https://prove2.me/submissions/1006eb56-a3f4-4f4d-bc3f-bc3c83bbf896

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_cellRes_mk_e362a206ff53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_cellRes_smul_e550401c6bb1

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
variable {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
theorem _root_.solution {J I : ∀ k, Finset (ι k)} (h : cellMon S J ≤ cellMon S I) (γ : K → ℤ)
    {x : LocalizedModule (cellMon S J) (MRingOver S ι ⧸ mIdealOver S y)}
    (hx : x ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S J) γ) :
    cellRes S _ J I x ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I) γ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [cellRes_mk h]
    exact Submodule.subset_span ⟨m, ⟨t.1, h t.2⟩, a, ht, hm, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul s x _ h' => rw [cellRes_smul]; exact Submodule.smul_mem _ s h'
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
