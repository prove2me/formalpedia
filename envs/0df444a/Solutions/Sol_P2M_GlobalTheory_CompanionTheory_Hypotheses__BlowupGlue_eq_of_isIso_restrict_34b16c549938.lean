-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__BlowupGlue_eq_of_isIso_restrict_34b16c549938
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:57:40.260393+00:00
-- url     : https://prove2.me/submissions/a6f4a427-7a96-4e95-9f89-4c3fce6528ac

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlowupOfAgreeingIdealCartier

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
theorem _root_.solution {X X' T : Scheme.{0}} {π : X' ⟶ X} {O : X.Opens} [IsIso (π ∣_ O)] (s : T ⟶ X')
    (c : T ⟶ O) (h : c ≫ O.ι = s ≫ π) : s = c ≫ inv (π ∣_ O) ≫ (π ⁻¹ᵁ O).ι := by
  have pb := isPullback_morphismRestrict π O
  have h₁ : pb.lift c s h ≫ (π ∣_ O) = c := pb.lift_fst c s h
  have h₂ : pb.lift c s h ≫ (π ⁻¹ᵁ O).ι = s := pb.lift_snd c s h
  rw [← h₁, Category.assoc, IsIso.hom_inv_id_assoc, h₂]
end GlobalTheory.CompanionTheory.Hypotheses₂.BlowupGlue
