-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_exists_homog_of_mem_quotPart_0d5b906c3b31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:26.374435+00:00
-- url     : https://prove2.me/submissions/96a2d674-4b43-4ff8-ab1b-e4f3d7170b8c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_zero_550d911f4552
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_add_c9d56145775a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellLocEval_isMultiHomog_smul_8e170cd1372f

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
variable {V : Ideal (MRingOver S ι)}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
theorem _root_.solution {d : K → ℤ} {m : MRingOver S ι ⧸ V} (hm : m ∈ quotPart S V d) :
    ∃ g : MRingOver S ι, IsMultiHomog g (fun k => (d k).toNat) ∧ ((∀ k, 0 ≤ d k) ∨ g = 0) ∧
      Ideal.Quotient.mk V g = m := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, ⟨hnn, hp⟩, rfl⟩ := hx
    exact ⟨p, hp, Or.inl hnn, rfl⟩
  | zero => exact ⟨0, isMultiHomog_zero _, Or.inr rfl, map_zero _⟩
  | add x x' _ _ h h' =>
    obtain ⟨g, hg, hd, rfl⟩ := h
    obtain ⟨g', hg', hd', rfl⟩ := h'
    refine ⟨g + g', isMultiHomog_add hg hg', ?_, map_add _ _ _⟩
    rcases hd with hd | rfl
    · exact Or.inl hd
    · rcases hd' with hd' | rfl
      · exact Or.inl hd'
      · exact Or.inr (add_zero 0)
  | smul s x _ h =>
    obtain ⟨g, hg, hd, rfl⟩ := h
    refine ⟨s • g, isMultiHomog_smul s hg, ?_, ?_⟩
    · rcases hd with hd | rfl
      · exact Or.inl hd
      · exact Or.inr (smul_zero s)
    · rw [← Ideal.Quotient.mkₐ_eq_mk S, map_smul]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellLocEval
