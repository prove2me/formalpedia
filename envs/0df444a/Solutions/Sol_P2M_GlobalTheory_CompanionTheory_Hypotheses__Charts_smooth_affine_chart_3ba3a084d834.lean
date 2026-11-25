-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__Charts_smooth_affine_chart_3ba3a084d834
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:52:40.203747+00:00
-- url     : https://prove2.me/submissions/84868920-64c4-4bc6-ab0f-d7f03232aade

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsSmoothAffinePresentationPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.Charts
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Charts
theorem _root_.solution {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k)
    (Z : X.IdealSheafData) (U : X.affineOpens) (hg : Smooth g) (hZ : Smooth (Z.subschemeι ≫ g)) :
    ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  let φ₀ : CommRingCat.of k ⟶ Γ(X, U.1) := Spec.preimage (U.2.fromSpec ≫ g)
  have h1 : Spec.map φ₀ = U.2.fromSpec ≫ g := Spec.map_preimage _
  refine ⟨φ₀.hom, ?_, ?_⟩
  · have : Smooth (Spec.map φ₀) := by
      rw [h1]
      exact @HasRingHomProperty.comp_of_isOpenImmersion @Smooth _ _ _ _ _ _ _
        (IsAffineOpen.isOpenImmersion_fromSpec (hU := U.2)) hg
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this
  · have hc : Z.subschemeCover.f U ≫ (Z.subschemeι ≫ g) =
        Spec.map (φ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal U))) := by
      rw [Spec.map_comp, h1, ← Category.assoc, Z.subschemeCover_map_subschemeι,
        Z.glueDataObjι_ι]
      exact Category.assoc _ _ _
    have : Smooth (Spec.map (φ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Z.ideal U)))) := by
      rw [← hc]
      exact @HasRingHomProperty.comp_of_isOpenImmersion @Smooth _ _ _ _ _ _ _
        (Z.subschemeCover.map_prop U) hZ
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mp this
end GlobalTheory.CompanionTheory.Hypotheses₂.Charts
