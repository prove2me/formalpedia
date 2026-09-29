-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_of_specMap_comp_eq_originChart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/9cd3b2c6-9a16-507b-a7c8-9e949be64910

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_of_specMap_comp_eq_originChart

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

namespace OriginLiftAux

theorem isLocalHom_of_ker_eq {T : Type u} [CommRing T] [IsLocalRing T] {K : Type u} [Field K]
    (π : T →+* K) (hπ : RingHom.ker π = maximalIdeal T) : IsLocalHom π := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hmem : a ∈ maximalIdeal T := (IsLocalRing.mem_maximalIdeal a).mpr hna
  rw [← hπ, RingHom.mem_ker] at hmem
  rw [hmem] at ha
  exact not_isUnit_zero ha

end OriginLiftAux

open OriginLiftAux

theorem solution
    {T : Type u} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve.Projective T) (P : Section W)
    {K : Type u} [Field K] (π : T →+* K) (hπ : RingHom.ker π = maximalIdeal T)
    (χbar : OriginChartRing W →+* K)
    (h : Spec.map (CommRingCat.ofHom π) ≫ P.1 = Spec.map (CommRingCat.ofHom χbar) ≫ originChartι W)
    (hx : χbar (xOverY W) = 0) (hz : χbar (zOverY W) = 0) :
    ∃ χ : OriginChartRing W →+* T, ReducesToOrigin P χ (maximalIdeal T) ∧ π.comp χ = χbar := by
  classical
  haveI : IsLocalHom (CommRingCat.ofHom π).hom := by
    rw [CommRingCat.hom_ofHom]; exact isLocalHom_of_ker_eq π hπ

  have hclosed : P.1 (closedPoint T) ∈ (originChartι W).opensRange := by
    rw [Scheme.Hom.mem_opensRange]
    refine ⟨Spec.map (CommRingCat.ofHom χbar) (closedPoint K), ?_⟩
    have e : (Spec.map (CommRingCat.ofHom π) ≫ P.1) (closedPoint K) =
        (Spec.map (CommRingCat.ofHom χbar) ≫ originChartι W) (closedPoint K) := by rw [h]
    simp only [Scheme.Hom.comp_apply] at e
    rw [Spec_closedPoint] at e
    exact e.symm
  have htop : P.1 ⁻¹ᵁ (originChartι W).opensRange = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem P.1 hclosed
  have hrange : Set.range P.1 ⊆ Set.range (originChartι W) := by
    rintro _ ⟨x, rfl⟩
    have hx' : x ∈ P.1 ⁻¹ᵁ (originChartι W).opensRange := by rw [htop]; trivial
    exact hx'

  set l := IsOpenImmersion.lift (originChartι W) P.1 hrange with hl_def
  have hl : l ≫ originChartι W = P.1 := IsOpenImmersion.lift_fac _ _ _
  set χ : OriginChartRing W →+* T := (Spec.preimage l).hom with hχ
  have hSpecχ : Spec.map (CommRingCat.ofHom χ) = l := by
    rw [hχ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hsec : IsOriginChartSection P χ := by
    show P.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W
    rw [hSpecχ, hl]

  have hcomp : π.comp χ = χbar := by
    have e1 : Spec.map (CommRingCat.ofHom π) ≫ l = Spec.map (CommRingCat.ofHom χbar) := by
      rw [← cancel_mono (originChartι W), Category.assoc, hl, h]
    have e2 : Spec.map (CommRingCat.ofHom (π.comp χ)) = Spec.map (CommRingCat.ofHom χbar) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, hSpecχ, e1]
    have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    simpa only [CommRingCat.hom_ofHom] using e3
  have hker : ∀ a, χbar a = 0 → χ a ∈ maximalIdeal T := fun a ha => by
    rw [← hπ, RingHom.mem_ker, ← RingHom.comp_apply, hcomp, ha]
  refine ⟨χ, ?_, hcomp⟩
  unfold ReducesToOrigin originParam originW
  exact ⟨hsec, (maximalIdeal T).neg_mem (hker _ hx), (maximalIdeal T).neg_mem (hker _ hz)⟩

end S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_of_specMap_comp_eq_originChart
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_of_specMap_comp_eq_originChart (solution)
