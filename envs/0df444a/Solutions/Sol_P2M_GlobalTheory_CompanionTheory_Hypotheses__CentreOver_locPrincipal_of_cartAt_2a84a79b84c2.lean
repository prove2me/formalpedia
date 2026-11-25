-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_locPrincipal_of_cartAt_2a84a79b84c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:29:46.411536+00:00
-- url     : https://prove2.me/submissions/69601c04-ef7e-4a13-87a3-bbbf6a14889c

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_EffCartierIffForallCartAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocPrincipalSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocallyPrincipalOfCartierAt
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CentreOver_exists_gen_of_map_eq_span_8fb85a512b0b

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
theorem _root_.solution : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), CartAt Z (U.2.fromSpec q) →
    LocPrincipal (Z.ideal U) q.asIdeal := by
  intro X _ Z U q hC
  obtain ⟨V, h, hxV, hh, hZV⟩ := hC
  have hxU : U.2.fromSpec q ∈ (U.1 : X.Opens) := by
    have hr : U.2.fromSpec q ∈ Set.range U.2.fromSpec := ⟨q, rfl⟩
    rw [U.2.range_fromSpec] at hr
    exact hr
  obtain ⟨f, g, hfg, hxf⟩ :=
    exists_basicOpen_le_affine_inter U.2 V.2 (U.2.fromSpec q) ⟨hxU, hxV⟩
  have hWU : X.basicOpen f ≤ U.1 := X.basicOpen_le f
  have hWV : X.basicOpen f ≤ V.1 := by
    rw [hfg]
    exact X.basicOpen_le g
  haveI : Nonempty (X.basicOpen f) := ⟨⟨_, hxf⟩⟩
  haveI : Nonempty (V.1 : X.Opens) := ⟨⟨_, hxV⟩⟩
  haveI : IsDomain Γ(X, V.1) := IsIntegral.component_integral V.1
  have hZW : Z.ideal (X.affineBasicOpen f) =
      Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom h} := by
    have hmap := Z.map_ideal (U := X.affineBasicOpen f) (V := V) hWV
    rw [hZV, Ideal.map_span, Set.image_singleton] at hmap
    first
      | exact hmap.symm
      | (rw [← hmap]; rfl)
      | (convert hmap.symm using 3)
  letI : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  haveI : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  have hb : (X.presheaf.map (homOfLE hWV).op).hom h ≠ 0 := by
    intro h0
    apply nonZeroDivisors.ne_zero hh
    apply map_injective_of_isIntegral X (homOfLE hWV)
    rw [map_zero]
    exact h0
  have hI : (Z.ideal U).map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) =
      Ideal.span {(X.presheaf.map (homOfLE hWV).op).hom h} := by
    rw [← hZW]
    first
      | exact Z.map_ideal (U := X.affineBasicOpen f) (V := U) hWU
      | exact Z.map_ideal_basicOpen U f
  obtain ⟨f0, hf0, hf0ne, hgen⟩ :=
    GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.exists_gen_of_map_eq_span f (Z.ideal U) _ hb hI
  refine ⟨f, f0, ?_, hf0, hf0ne, hgen⟩
  have hq : q ∈ PrimeSpectrum.basicOpen f :=
    Eq.mp (congrArg (q ∈ ·) (U.2.fromSpec_preimage_basicOpen f)) hxf
  exact (PrimeSpectrum.mem_basicOpen f q).mp hq
end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
