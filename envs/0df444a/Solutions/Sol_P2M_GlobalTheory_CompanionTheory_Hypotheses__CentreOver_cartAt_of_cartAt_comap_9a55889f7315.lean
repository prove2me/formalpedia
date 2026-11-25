-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_cartAt_comap_9a55889f7315
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:00:20.365596+00:00
-- url     : https://prove2.me/submissions/36e3fb12-74bb-440b-a05a-f2121f045252

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierRestrictIffCartierAt
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
theorem _root_.solution {X Y : Scheme.{0}} (J : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (x : X) (h : CartAt (J.comap f) x) : CartAt J (f x) := by
  obtain ⟨U, g, hxU, hg, hJ⟩ := h
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen (f ''ᵁ U.1) := hU.image_of_isOpenImmersion f
  refine ⟨⟨f ''ᵁ U.1, hV⟩, (f.appIso U.1).inv.hom g, ⟨x, hxU, rfl⟩, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors (f.appIso U.1).symm.commRingCatIsoToRingEquiv hg
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hJ
    have hs : Function.Surjective (f.appIso U.1).inv.hom :=
      (f.appIso U.1).symm.commRingCatIsoToRingEquiv.surjective
    rw [← Ideal.map_comap_of_surjective _ hs (J.ideal ⟨f ''ᵁ U.1, hV⟩), hJ, Ideal.map_span,
      Set.image_singleton]
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
