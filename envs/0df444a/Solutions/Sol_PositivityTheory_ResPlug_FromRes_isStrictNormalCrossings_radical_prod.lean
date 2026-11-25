-- Prove2me | solution 1 for PositivityTheory.ResPlug.FromRes.isStrictNormalCrossings_radical_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:25:18.4218+00:00
-- url     : https://prove2.me/submissions/d2cd7be7-8e2c-4d7f-a811-232c17c77577

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Statements
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsClopen
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsOpenImmersion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_WeilBound_CoreStatements_ResolutionCharZero_FromResSnc
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_Blowup_IsBlowupAlongIdealSheaf_restrict
import Theorems.Thm_FunctorialResolution_Blowup_idealSheafData_prod_cons
import Theorems.Thm_FunctorialResolution_Blowup_idealSheafData_prod_nil
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebraMap_eq_coordRingHom
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebra_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coord_restrict
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_etaleChartCoord_injective
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart_coord_mem_primeIdealOf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_isRegularParameterSystem_with_coords_of_mem_prime
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_maximalIdeal_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRadical_span_singleton_prod_etaleChartCoord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_stalk_of_smooth
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_top_of_le
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
namespace PositivityTheory.ResPlug.FromRes
open FunctorialResolution FunctorialResolution.EmbeddedResolution
private theorem ideal_top {X : Scheme.{0}} (U : X.affineOpens) :
    (⊤ : X.IdealSheafData).ideal U = ⊤ := by simp
private theorem ideal_comap_mul {X Y : Scheme.{0}} (g : X ⟶ Y) (U : Y.affineOpens)
    (V : X.affineOpens) (e : (V : X.Opens) ≤ g ⁻¹ᵁ (U : Y.Opens)) (I J : Y.IdealSheafData) :
    ((I * J).comap g).ideal V = (I.comap g).ideal V * (J.comap g).ideal V := by
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (I * J) g U V e,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I g U V e,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE J g U V e,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]
private theorem ι_appLE_top_eq_topIso_inv {Y : Scheme.{0}} (V : Y.Opens) :
    V.ι.appLE V ⊤ (top_le_ι_preimage_self V) = V.topIso.inv := by
  simp
  rfl
private theorem ι_appLE_top_bijective {Y : Scheme.{0}} (V : Y.Opens) :
    Function.Injective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) ∧
      Function.Surjective (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V))) := by
  rw [ι_appLE_top_eq_topIso_inv]
  exact V.topIso.commRingCatIsoToRingEquiv.symm.bijective
private theorem ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top {Y : Scheme.{0}} (D : Y.IdealSheafData)
    {V : Y.Opens} (hV : IsAffineOpen V) (htop : restrictIdeal D V = ⊤) :
    D.ideal ⟨V, hV⟩ = ⊤ := by
  have : IsAffine V.toScheme := hV
  have key := Scheme.IdealSheafData.comap_ideal_eq_map_appLE D V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_ι_preimage_self V)
  rw [← restrictIdeal_eq_comap_ι, htop] at key
  have h0 : ((⊤ : V.toScheme.IdealSheafData).ideal ⟨⊤, isAffineOpen_top V.toScheme⟩) = ⊤ := by
    simp
  rw [h0] at key
  have key2 : Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V)))
      (D.ideal ⟨V, hV⟩) = ⊤ := key.symm
  have hbij := ι_appLE_top_bijective V
  have hcomap : Ideal.comap (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V)))
      (Ideal.map (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_ι_preimage_self V)))
        (D.ideal ⟨V, hV⟩)) = D.ideal ⟨V, hV⟩ := by
    apply Ideal.comap_map_of_bijective
    exact hbij
  rw [key2, Ideal.comap_top] at hcomap
  exact hcomap.symm
private theorem etaleChartCoord_eq_coord {X : Scheme.{0}} {k : Type} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {V : X.Opens} {m : ℕ} (c : EtaleChart p V m) (j : Fin m) :
    @etaleChartCoord k _ m Γ(X, V) _ c.algebra j = c.coord j := by
  rw [etaleChartCoord_def, c.algebraMap_eq_coordRingHom, c.coordRingHom_X]
private theorem presheaf_map_mem_primeIdealOf {X : Scheme.{0}} {V V' : X.Opens}
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V) (x : ↥X)
    (hxV : x ∈ V) (hxV' : x ∈ V') (s : Γ(X, V))
    (hs : s ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) :
    (X.presheaf.map (homOfLE hle).op).hom s ∈ (hV'.primeIdealOf ⟨x, hxV'⟩).asIdeal := by
  have hres : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ V' x hxV'
      = X.presheaf.germ V x hxV := X.presheaf.germ_res (homOfLE hle) x hxV'
  have hgerm := congrArg
    (fun φ : Γ(X, V) ⟶ X.presheaf.stalk x => CommRingCat.Hom.hom φ s) hres
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hgerm
  have h1 : X.presheaf.germ V x hxV s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (germ_mem_maximalIdeal_iff hV x hxV s).mpr hs
  refine (germ_mem_maximalIdeal_iff hV' x hxV' _).mp ?_
  show (X.presheaf.germ V' x hxV').hom ((X.presheaf.map (homOfLE hle).op).hom s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  rw [hgerm]
  exact h1
private theorem exists_finset_comap_prod_ideal_eq_span_prod_coord {Y W : Scheme.{0}} {k : Type}
    [Field k] {pY : Y ⟶ Spec (CommRingCat.of k)} (g : Y ⟶ W) (U : W.affineOpens) {V : Y.Opens}
    (hV : IsAffineOpen V) (e : V ≤ g ⁻¹ᵁ (U : W.Opens)) {n : ℕ} (c : EtaleChart pY V n) :
    ∀ (F : List W.IdealSheafData) (γ : ℕ → Option (Fin n)),
      (∀ i, ∀ h : i < F.length, γ i = none → restrictIdeal ((F[i]'h).comap g) V = ⊤) →
      (∀ i, ∀ h : i < F.length, ∀ j, γ i = some j →
        restrictIdeal ((F[i]'h).comap g) V = c.coordIdeal {j}) →
      (∀ i i', i < F.length → i' < F.length → ∀ j, γ i = some j → γ i' = some j → i = i') →
      ∃ J : Finset (Fin n),
        (∀ j ∈ J, ∃ i, ∃ _ : i < F.length, γ i = some j) ∧
        (F.prod.comap g).ideal ⟨V, hV⟩ = Ideal.span {∏ j ∈ J, c.coord j} := by
  intro F
  induction F with
  | nil =>
      intro γ _ _ _
      refine ⟨∅, by simp, ?_⟩
      have h1 : (([] : List W.IdealSheafData).prod).comap g = (⊤ : Y.IdealSheafData) := by
        rw [Blowup.idealSheafData_prod_nil]
        simp
      rw [h1, Finset.prod_empty, Ideal.span_singleton_one]
      exact ideal_top _
  | cons D F ih =>
      intro γ hnone hsome hinj
      have hlen : ∀ i, i < F.length → i + 1 < (D :: F).length := by
        intro i hi
        simp only [List.length_cons]
        omega
      have hD0 : (0 : ℕ) < (D :: F).length := by
        simp only [List.length_cons]
        omega
      obtain ⟨J', hJ'mem, hJ'⟩ := ih (fun i => γ (i + 1))
        (fun i h hg => hnone (i + 1) (hlen i h) hg)
        (fun i h j hg => hsome (i + 1) (hlen i h) j hg)
        (fun i i' hi hi' j h1 h2 => by
          have h3 := hinj (i + 1) (i' + 1) (hlen i hi) (hlen i' hi') j h1 h2
          omega)
      have hprod : ((D :: F).prod.comap g).ideal ⟨V, hV⟩
          = (D.comap g).ideal ⟨V, hV⟩ * ((F.prod).comap g).ideal ⟨V, hV⟩ := by
        rw [Blowup.idealSheafData_prod_cons]
        exact ideal_comap_mul g U ⟨V, hV⟩ e D F.prod
      cases hγ0 : γ 0 with
      | none =>
          have hD : (D.comap g).ideal ⟨V, hV⟩ = ⊤ :=
            ideal_eq_top_of_isAffineOpen_of_restrictIdeal_eq_top _ hV (hnone 0 hD0 hγ0)
          refine ⟨J', ?_, ?_⟩
          · intro j hj
            obtain ⟨i, hi, hγi⟩ := hJ'mem j hj
            exact ⟨i + 1, hlen i hi, hγi⟩
          · rw [hprod, hD, hJ', Ideal.top_mul]
      | some j0 =>
          have hD : (D.comap g).ideal ⟨V, hV⟩ = Ideal.span {c.coord j0} := by
            have h2 := EtaleChart.ideal_eq_span_coord c hV (D.comap g) {j0}
              (hsome 0 hD0 j0 hγ0)
            rw [Finset.coe_singleton, Set.image_singleton] at h2
            exact h2
          have hj0 : j0 ∉ J' := by
            intro hj0mem
            obtain ⟨i, hi, hγi⟩ := hJ'mem j0 hj0mem
            have h3 := hinj 0 (i + 1) hD0 (hlen i hi) j0 hγ0 hγi
            omega
          refine ⟨insert j0 J', ?_, ?_⟩
          · intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj'
            · exact ⟨0, hD0, hγ0⟩
            · obtain ⟨i, hi, hγi⟩ := hJ'mem j hj'
              exact ⟨i + 1, hlen i hi, hγi⟩
          · rw [hprod, hD, hJ', Ideal.span_singleton_mul_span_singleton,
              Finset.prod_insert hj0]
end PositivityTheory.ResPlug.FromRes
end
end

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open PositivityTheory PositivityTheory.ResPlug PositivityTheory.ResPlug.FromRes
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace PositivityTheory.ResPlug.FromRes
theorem _root_.solution {W : Scheme.{0}} {k : Type} [Field k]
    (p : W ⟶ Spec (CommRingCat.of k)) [Smooth p] (E : List W.IdealSheafData)
    (hE : InStrictNormalCrossingPosition p E) : IsStrictNormalCrossings E.prod.radical := by
  have hid : E.prod.comap (𝟙 W) = E.prod := Scheme.IdealSheafData.comap_id _
  rw [← hid]
  intro y
  obtain ⟨U0, sectionFrameQuotient, m, c0, a, h1, h2, h3⟩ := hE.2 y
  obtain ⟨V0, hV0, hyV0, hV0le⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens W) sectionFrameQuotient
  obtain ⟨V, hV, hyV, n, c, γ, hγ, hinjγ, hmem⟩ :=
    exists_etaleChart_coord_mem_primeIdealOf E y V0 hV0 hyV0 (c0.restrict hV0le) a
      (fun i hi => ⟨fun hg => restrictIdeal_eq_top_of_le _ hV0le (h2 i hi hg),
        fun j hg => restrictIdeal_eq_restrict_coordIdeal_of_le hV0le c0 _ {j} (h3 i hi j hg)⟩)
      (fun i i' hi hi' j hj hj' => h1 i hi i' hi' j hj hj')
  have hyU : (𝟙 W : W ⟶ W).base y ∈ V := hyV
  have hyVU : y ∈ (V ⊓ (𝟙 W : W ⟶ W) ⁻¹ᵁ V : W.Opens) := ⟨hyV, hyU⟩
  obtain ⟨fs, hfle, hyf⟩ := hV.exists_basicOpen_le ⟨y, hyVU⟩ hyV
  obtain ⟨V', hV', hV'V, hV'U, hyV'⟩ :
      ∃ V' : W.Opens, IsAffineOpen V' ∧ V' ≤ V ∧ V' ≤ (𝟙 W : W ⟶ W) ⁻¹ᵁ V ∧ y ∈ V' :=
    ⟨W.basicOpen fs, hV.basicOpen fs, le_trans hfle inf_le_left, le_trans hfle inf_le_right, hyf⟩
  have hγ' : ∀ i, ∀ h : i < E.length,
      (γ i = none → restrictIdeal ((E[i]'h).comap (𝟙 W)) V' = ⊤) ∧
      (∀ j, γ i = some j →
        restrictIdeal ((E[i]'h).comap (𝟙 W)) V' = (c.restrict hV'V).coordIdeal {j}) := by
    intro i h
    rw [Scheme.IdealSheafData.comap_id]
    refine ⟨fun hg => restrictIdeal_eq_top_of_le _ hV'V ((hγ i h).1 hg), fun j hg => ?_⟩
    exact restrictIdeal_eq_restrict_coordIdeal_of_le hV'V c _ {j} ((hγ i h).2 j hg)
  obtain ⟨J₀, hJ₀mem, hJ₀⟩ :=
    exists_finset_comap_prod_ideal_eq_span_prod_coord (𝟙 W) ⟨V, hV⟩ hV' hV'U
      (c.restrict hV'V) E γ (fun i h => (hγ' i h).1) (fun i h => (hγ' i h).2) hinjγ
  have hJ₀prime : ∀ j ∈ J₀,
      (c.restrict hV'V).coord j ∈ (hV'.primeIdealOf ⟨y, hyV'⟩).asIdeal := by
    intro j hj
    obtain ⟨i, hi, hγi⟩ := hJ₀mem j hj
    rw [FunctorialResolution.EmbeddedResolution.EtaleChart.coord_restrict c hV'V j]
    exact presheaf_map_mem_primeIdealOf hV hV' hV'V y hyV hyV' (c.coord j) (hmem i hi j hγi)
  have hntr : Nontrivial ↥(W.presheaf.obj (op V')) := by
    rcases subsingleton_or_nontrivial ↥(W.presheaf.obj (op V')) with hs | hs
    · exfalso
      refine (hV'.primeIdealOf ⟨y, hyV'⟩).isPrime.ne_top ?_
      rw [Ideal.eq_top_iff_one]
      have h10 : (1 : ↥(W.presheaf.obj (op V'))) = 0 := @Subsingleton.elim _ hs 1 0
      rw [h10]
      exact Submodule.zero_mem _
    · exact hs
  have hcinj : Function.Injective (c.restrict hV'V).coord := by
    have h := @etaleChartCoord_injective k _ n ↥(W.presheaf.obj (op V')) _
      (c.restrict hV'V).algebra ((c.restrict hV'V).algebra_etale hV') hntr
    intro a b hab
    refine h ?_
    simp only [etaleChartCoord_eq_coord]
    exact hab
  have hrad := @isRadical_span_singleton_prod_etaleChartCoord k _ n
    ↥(W.presheaf.obj (op V')) _ (c.restrict hV'V).algebra
    ((c.restrict hV'V).algebra_etale hV') J₀
  simp only [etaleChartCoord_eq_coord] at hrad
  obtain ⟨N, f, hfcoord, hfreg⟩ :=
    exists_isRegularParameterSystem_with_coords_of_mem_prime hV' (c.restrict hV'V) y hyV'
      J₀ hJ₀prime
  choose ι hι using hfcoord
  have hinj2 : ∀ a ∈ J₀.attach, ∀ b ∈ J₀.attach,
      (fun j : { x // x ∈ J₀ } => ι j.1 j.2) a = (fun j : { x // x ∈ J₀ } => ι j.1 j.2) b →
        a = b := by
    intro a _ b _ hab
    have h1 : (c.restrict hV'V).coord a.1 = (c.restrict hV'V).coord b.1 := by
      rw [← hι a.1 a.2, ← hι b.1 b.2]
      exact congrArg f hab
    exact Subtype.ext (hcinj h1)
  have hprodJ : (∏ i ∈ J₀.attach.image (fun j : { x // x ∈ J₀ } => ι j.1 j.2), f i)
      = ∏ j ∈ J₀, (c.restrict hV'V).coord j := by
    rw [Finset.prod_image hinj2, ← Finset.prod_attach J₀ (fun j => (c.restrict hV'V).coord j)]
    exact Finset.prod_congr rfl fun j _ => hι j.1 j.2
  refine ⟨isRegularLocalRing_stalk_of_smooth p y,
    ⟨V', hV'⟩, hyV', N, f, J₀.attach.image (fun j : { x // x ∈ J₀ } => ι j.1 j.2), hfreg, ?_⟩
  rw [Scheme.IdealSheafData.radical_ideal, hJ₀, hrad.radical, hprodJ]
end PositivityTheory.ResPlug.FromRes
