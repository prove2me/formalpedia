-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_effCartier_comap_opens_iff_53f9aad034ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:44:45.583943+00:00
-- url     : https://prove2.me/submissions/3806b4f9-3551-45f8-beed-a35d26d867e4

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierRestrictIffCartierAt
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_of_cartAt_comap_9a55889f7315
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_cartAt_comap_of_cartAt_d19af1b79604
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_effCartier_iff_forall_cartAt_7444c988f6eb


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
theorem _root_.solution : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (O : X.Opens),
    FinalTheorems.EffCartier (J.comap O.ι) ↔ ∀ x ∈ O, CartAt J x := by
  intro X J O
  rw [effCartier_iff_forall_cartAt]
  constructor
  · intro h x hx
    exact cartAt_of_cartAt_comap J O.ι ⟨x, hx⟩ (h ⟨x, hx⟩)
  · intro h x
    exact cartAt_comap_of_cartAt J O.ι x (h x.1 x.2)
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
