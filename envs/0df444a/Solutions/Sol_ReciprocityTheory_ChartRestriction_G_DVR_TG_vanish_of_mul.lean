-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.vanish_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:03.825445+00:00
-- url     : https://prove2.me/submissions/f3bf5d64-46b2-4f9b-86d2-7a56e87494e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenThick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_toW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_toW_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_appLE_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_fst_tq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_mul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R]
variable [IsDomain R]
set_option maxHeartbeats 400000
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) [Flat p] {a : R} (ha : a ≠ 0)
    (e : ℕ) {J₁ J₂ : Ideal R} (h1 : J₁ ≤ Ideal.span {a ^ (e + 2)}) (h2 : a ^ (e + 1) ∈ J₂)
    (ι : pullback p (tq J₂) ⟶ pullback p (tq J₁)) (hι : ι ≫ pullback.fst p (tq J₁) = pullback.fst p (tq J₂))
    (V : (pullback p (tq J₁)).Opens) (y : Γ(pullback p (tq J₁), V))
    (hy : toW (pullback.fst p (tq J₁) ≫ p) V a * y = 0) :
    (ι.app V) y = 0 := by
  set π₁ := pullback.fst p (tq J₁)
  set π₂ := pullback.fst p (tq J₂)
  have : IsClosedImmersion (tq J₁) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion π₁ := inferInstance
  refine TopCat.Presheaf.section_ext (pullback p (tq J₂)).sheaf _ _ 0 fun z hz => ?_

  have hemb : Topology.IsEmbedding π₁.base := π₁.isClosedEmbedding.isEmbedding
  obtain ⟨V₀, hV₀, hV₀e⟩ := hemb.isInducing.isOpen_iff.1 V.isOpen
  have hz0 : π₁.base (ι.base z) ∈ V₀ := by
    have : ι.base z ∈ (π₁.base ⁻¹' V₀) := by rw [hV₀e]; exact hz
    exact this
  obtain ⟨W, hW, hzW, hWV₀⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show π₁.base (ι.base z) ∈ (⟨V₀, hV₀⟩ : X.Opens) from hz0)
  have hWV : π₁ ⁻¹ᵁ W ≤ V := by
    intro u hu
    have : u ∈ π₁.base ⁻¹' V₀ := hWV₀ hu
    rw [hV₀e] at this; exact this

  obtain ⟨hs, hk⟩ := app_fst_tq p J₁ W hW
  obtain ⟨yt, hyt⟩ := hs (((pullback p (tq J₁)).presheaf.map (homOfLE hWV).op).hom y)
  have hay : π₁.app W (toW p W a * yt) = 0 := by
    rw [map_mul, hyt, app_toW, ← toW_res (π₁ ≫ p) hWV, ← map_mul, hy, map_zero]
  have hm := Ideal.map_mono h1 (hk _ hay)
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, hc⟩ := hm
  have hyt' : yt = toW p W (a ^ (e + 1)) * c := by
    apply sub_eq_zero.1
    apply toW_mul_eq_zero p W ha
    rw [mul_sub, ← hc, map_pow, map_pow, pow_succ' _ (e + 1)]
    ring

  have hW2 : π₂ ⁻¹ᵁ W ≤ ι ⁻¹ᵁ V := by
    intro u hu
    apply hWV
    show π₁.base (ι.base u) ∈ W
    rw [← Scheme.Hom.comp_apply, hι]; exact hu
  have hW2' : π₂ ⁻¹ᵁ W ≤ ι ⁻¹ᵁ (π₁ ⁻¹ᵁ W) := by
    intro u hu
    show π₁.base (ι.base u) ∈ W
    rw [← Scheme.Hom.comp_apply, hι]; exact hu
  have hzW2 : z ∈ π₂ ⁻¹ᵁ W := by
    show π₂.base z ∈ W
    rw [← hι, Scheme.Hom.comp_apply]; exact hzW
  have e5 : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) = (π₂.app W) yt := by
    have a1 : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) =
        (ι.appLE V (π₂ ⁻¹ᵁ W) hW2) y := by
      rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]
      erw [Scheme.Hom.appLE_map]
    have a2 : (ι.appLE V (π₂ ⁻¹ᵁ W) hW2) y =
        (ι.appLE (π₁ ⁻¹ᵁ W) (π₂ ⁻¹ᵁ W) hW2') (((pullback p (tq J₁)).presheaf.map (homOfLE hWV).op).hom y) := by
      rw [← CommRingCat.comp_apply]
      erw [Scheme.Hom.map_appLE]
    have a3 : (ι.appLE (π₁ ⁻¹ᵁ W) (π₂ ⁻¹ᵁ W) hW2') ((π₁.app W) yt) = (π₂.app W) yt := by
      rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply]
      erw [Scheme.Hom.appLE_comp_appLE]
      rw [appLE_of_eq hι, Scheme.Hom.app_eq_appLE]
    rw [a1, a2, ← hyt, a3]
  have hzero : ((pullback p (tq J₂)).presheaf.map (homOfLE hW2).op).hom ((ι.app V) y) = 0 := by
    rw [e5, hyt', map_mul, app_toW_of_mem p J₂ W h2, zero_mul]
  show (pullback p (tq J₂)).presheaf.germ _ z hz ((ι.app V) y) = (pullback p (tq J₂)).presheaf.germ _ z hz 0
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hW2) z hzW2, hzero, map_zero, map_zero]
end ReciprocityTheory.ChartRestriction.G.DVR.TG
