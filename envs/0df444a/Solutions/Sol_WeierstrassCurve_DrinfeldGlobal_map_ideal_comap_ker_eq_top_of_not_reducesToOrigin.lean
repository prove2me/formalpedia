-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.map_ideal_comap_ker_eq_top_of_not_reducesToOrigin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f4bbcf91-6afe-5ef3-9a32-67e5c190ee18

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_eq_top_of_not_reducesToOrigin

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization in
set_option maxHeartbeats 3200000 in
theorem solution
    {T : Type u} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve T) (P : Section W)
    (hP : ∀ χ : OriginChartRing W →+* T, ¬ ReducesToOrigin P χ (maximalIdeal T))
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    Ideal.map (Φ.comp (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom)
      (((Scheme.Hom.ker P.1).comap (originChartι W)).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) = ⊤ := by
  classical
  by_contra hne

  set χ₀ : OriginChartRing W →+* T := (PowerSeries.constantCoeff (R := T)).comp Φ with hχ₀
  have hsc₀ : ∀ t : T, χ₀ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t := by
    intro t; rw [hχ₀, RingHom.comp_apply, hΦsc, PowerSeries.constantCoeff_C]
  have hx₀ : χ₀ (xOverY W) = 0 := by rw [hχ₀, RingHom.comp_apply, hΦx, map_neg, PowerSeries.constantCoeff_X, neg_zero]
  have hz₀ : χ₀ (zOverY W) = 0 := by rw [hχ₀, RingHom.comp_apply, hΦz, map_neg, W.constantCoeff_formalW, neg_zero]

  set J := ((Scheme.Hom.ker P.1).comap (originChartι W)).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ with hJ
  have hJm : ∀ f ∈ J, χ₀ ((Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).hom.hom f) ∈ maximalIdeal T := by
    intro f hf
    by_contra hu
    replace hu := IsLocalRing.notMem_maximalIdeal.mp hu
    apply hne
    apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
    rw [RingHom.comp_apply, PowerSeries.isUnit_iff_constantCoeff]
    simpa [hχ₀] using hu

  set x₀ : ↥(Spec (CommRingCat.of (OriginChartRing W))) := (Spec.map (CommRingCat.ofHom χ₀)).base (closedPoint T) with hx₀def
  have hx₀I : ∀ a : OriginChartRing W, a ∈ x₀.asIdeal ↔ χ₀ a ∈ maximalIdeal T := by
    intro a; rw [hx₀def]; rfl

  have hsupp : x₀ ∈ ((Scheme.Hom.ker P.1).comap (originChartι W)).support := by
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩)
      (by trivial), Scheme.mem_zeroLocus_iff]
    intro f hf
    rw [AlgebraicGeometry.basicOpen_eq_of_affine']
    change ¬ ((x₀ : PrimeSpectrum (OriginChartRing W)) ∈ PrimeSpectrum.basicOpen _)
    erw [PrimeSpectrum.mem_basicOpen, not_not]
    exact (hx₀I _).mpr (hJm f hf)

  haveI : IsSeparated (projModelStrCR W) := by delta projModelStrCR; infer_instance
  haveI : IsClosedImmersion P.1 := by
    have : IsClosedImmersion (P.1 ≫ projModelStrCR W) := by rw [P.2]; infer_instance
    exact IsClosedImmersion.of_comp (g := projModelStrCR W) _
  have hrangeP : (originChartι W).base x₀ ∈ Set.range P.1.base := by
    rw [Scheme.IdealSheafData.support_comap] at hsupp
    have h1 : (originChartι W).base x₀ ∈ ((Scheme.Hom.ker P.1).support : Set _) := hsupp
    rw [Scheme.Hom.support_ker, P.1.isClosedEmbedding.isClosed_range.closure_eq] at h1
    exact h1
  obtain ⟨y, hy⟩ := hrangeP

  have hsect : χ₀.comp ((fromZeroRingHom (projModelGradingCR W) _).comp (algebraMap T ((projModelGradingCR W) 0))) =
      RingHom.id T := RingHom.ext fun t => by simpa using hsc₀ t
  have hstr₀ : Spec.map (CommRingCat.ofHom χ₀) ≫ originChartι W ≫ projModelStrCR W = 𝟙 _ := by
    simp only [originChartι, projModelStrCR, Category.assoc]
    rw [← Category.assoc (Proj.awayι ..), Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hsect, CommRingCat.ofHom_id, Spec.map_id]
  have hy' : y = closedPoint T := by
    have h1 : (P.1 ≫ projModelStrCR W).base y = y := by rw [P.2]; rfl
    have h2 : (projModelStrCR W).base (P.1.base y) = (projModelStrCR W).base ((originChartι W).base x₀) := by rw [hy]
    have h3 : (projModelStrCR W).base ((originChartι W).base x₀) = closedPoint T := by
      change (Spec.map (CommRingCat.ofHom χ₀) ≫ originChartι W ≫ projModelStrCR W).base (closedPoint T) = closedPoint T
      rw [hstr₀]; rfl
    rw [← h1]
    exact h2.trans h3
  subst hy'

  have hrange : Set.range P.1.base ⊆ Set.range (originChartι W).base := by
    rintro _ ⟨y', rfl⟩
    have hsp : P.1.base y' ⤳ P.1.base (closedPoint T) :=
      (IsLocalRing.specializes_closedPoint y').map P.1.base.hom.continuous
    rw [hy] at hsp
    exact hsp.mem_open (originChartι W).isOpenEmbedding.isOpen_range ⟨x₀, rfl⟩
  let g : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (OriginChartRing W)) :=
    IsOpenImmersion.lift (originChartι W) P.1 hrange
  have hg : g ≫ originChartι W = P.1 := IsOpenImmersion.lift_fac _ _ hrange
  let χ : OriginChartRing W →+* T :=
    ((Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom.comp g.appTop.hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).inv.hom
  have hχ : Spec.map (CommRingCat.ofHom χ) = g := by
    change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of (OriginChartRing W))).inv ≫ g.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of T)).hom) = g
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← Scheme.isoSpec_Spec_hom,
      Category.assoc, Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have hsecχ : IsOriginChartSection P χ := by unfold IsOriginChartSection; rw [hχ, hg]

  have hpt : (Spec.map (CommRingCat.ofHom χ)).base (closedPoint T) = x₀ := by
    apply (originChartι W).isOpenEmbedding.injective
    rw [← hy]
    change (Spec.map (CommRingCat.ofHom χ) ≫ originChartι W).base (closedPoint T) = P.1.base (closedPoint T)
    rw [hχ, hg]
  have hmem : ∀ a : OriginChartRing W, χ₀ a = 0 → χ a ∈ maximalIdeal T := by
    intro a ha
    have : a ∈ x₀.asIdeal := by rw [hx₀I, ha]; exact (maximalIdeal T).zero_mem
    rw [← hpt] at this
    exact this
  exact hP χ ⟨hsecχ, (maximalIdeal T).neg_mem (hmem _ hx₀), (maximalIdeal T).neg_mem (hmem _ hz₀)⟩

end S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_eq_top_of_not_reducesToOrigin
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ideal_comap_ker_eq_top_of_not_reducesToOrigin (solution)
