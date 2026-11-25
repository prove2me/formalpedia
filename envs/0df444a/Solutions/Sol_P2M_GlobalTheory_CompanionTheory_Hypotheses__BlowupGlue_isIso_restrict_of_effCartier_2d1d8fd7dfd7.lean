-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_isIso_restrict_of_effCartier_2d1d8fd7dfd7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:04.750531+00:00
-- url     : https://prove2.me/submissions/dca8f361-8883-4641-958e-a5594f79b1fa

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartier
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_effCartier_comap_of_isOpenImmersion__bb69f67b52e9


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
theorem _root_.solution {X X' : Scheme.{0}} {π : X' ⟶ X} {J : X.IdealSheafData} (h : FinalTheorems.Blowup π J)
    (U : X.Opens) (hU : FinalTheorems.EffCartier (J.comap U.ι)) : IsIso (π ∣_ U) := by
  obtain ⟨σ, hσ, -⟩ := h.2 U U.ι hU
  have pb := isPullback_morphismRestrict π U
  have hc : FinalTheorems.EffCartier (J.comap ((π ⁻¹ᵁ U).ι ≫ π)) := by
    rw [Scheme.IdealSheafData.comap_comp]; exact effCartier_comap_of_isOpenImmersion' _ _ h.1
  obtain ⟨τ, -, hτ⟩ := h.2 (π ⁻¹ᵁ U) ((π ⁻¹ᵁ U).ι ≫ π) hc
  have e : π ∣_ U ≫ σ = (π ⁻¹ᵁ U).ι :=
    (hτ _ (by simp [hσ])).trans (hτ _ rfl).symm
  exact ⟨pb.lift (𝟙 _) σ (by simp [hσ]), pb.hom_ext (by simp) (by simp [e]), by simp⟩
end GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
