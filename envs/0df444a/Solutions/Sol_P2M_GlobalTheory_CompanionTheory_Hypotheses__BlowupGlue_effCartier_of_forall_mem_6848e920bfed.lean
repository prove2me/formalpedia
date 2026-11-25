-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_effCartier_of_forall_mem_6848e920bfed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:58:54.950396+00:00
-- url     : https://prove2.me/submissions/9eb0e871-1cef-4c1b-a834-c4e198852422

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartier
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringEquiv_mem_nonZeroDivisors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
namespace GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
theorem _root_.solution {X : Scheme.{0}} (I : X.IdealSheafData)
    (h : ∀ x : X, ∃ O : X.Opens, x ∈ O ∧ FinalTheorems.EffCartier (I.comap O.ι)) : FinalTheorems.EffCartier I := by
  intro x
  obtain ⟨O, hx, hO⟩ := h x
  obtain ⟨U, f, hxU, hf, hU⟩ := hO ⟨x, hx⟩
  have hV : IsAffineOpen (O.ι ''ᵁ U.1) := U.2.image_of_isOpenImmersion O.ι
  let e := (O.ι.appIso U.1).commRingCatIsoToRingEquiv
  refine ⟨⟨_, hV⟩, e.symm f, ⟨_, hxU, rfl⟩, ringEquiv_mem_nonZeroDivisors e.symm hf, ?_⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hU
  have hs : Function.Surjective ((O.ι.appIso U.1).inv.hom : _ →+* _) := e.symm.surjective
  have := Ideal.map_comap_of_surjective _ hs (I.ideal ⟨O.ι ''ᵁ U.1, hV⟩)
  rw [hU, Ideal.map_span, Set.image_singleton] at this
  exact this.symm
end GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
