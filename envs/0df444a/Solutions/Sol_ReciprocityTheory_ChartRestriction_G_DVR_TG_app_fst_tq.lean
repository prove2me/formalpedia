-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TG.app_fst_tq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:35.74203+00:00
-- url     : https://prove2.me/submissions/ccdea5c7-068f-41b4-8c83-f942e161cab4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_pushout_quot

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
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (W : X.Opens)
    (hW : IsAffineOpen W) :
    Function.Surjective ((pullback.fst p (tq J)).app W) ∧
      ∀ x, (pullback.fst p (tq J)).app W x = 0 → x ∈ J.map (toW p W) := by
  have H := IsPullback.of_hasPullback p (tq J)
  have hUST : tq J ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ tq J ⁻¹ᵁ ⊤ := le_rfl
  have hUSX : W ≤ p ⁻¹ᵁ ⊤ := le_top
  have hUY : pullback.fst p (tq J) ⁻¹ᵁ W =
      pullback.fst p (tq J) ⁻¹ᵁ W ⊓ pullback.snd p (tq J) ⁻¹ᵁ (tq J ⁻¹ᵁ ⊤) := by
    simp
  have hT : IsAffineOpen (tq J ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens)) := by
    simpa using isAffineOpen_top (Spec (CommRingCat.of (R ⧸ J)))
  have iso := isIso_pushoutSection_of_isAffineOpen H hUST hUSX hUY (isAffineOpen_top _) hT hW
  have hP := (isIso_pushoutSection_iff H hUST hUSX hUY).1 iso
  have hb0 : (tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) hUST =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv := by
    rw [Scheme.Hom.appLE_eq_app, ← Scheme.Hom.appTop,
      (Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk J))),
      Category.assoc]
  have eR : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = r :=
    fun r => by rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
  have eR' : ∀ z, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom z) = z :=
    fun z => by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have eS : ∀ y, (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom y) = y :=
    fun y => by rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have hbapp : ∀ z, ((tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) hUST).hom z =
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv.hom
        (Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom z)) := fun z => by
    rw [hb0]; rfl
  have hb : Function.Surjective ((tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) hUST) := by
    intro y
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom y)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r, ?_⟩
    show ((tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) hUST).hom _ = y
    rw [hbapp, eR, hr]
    exact eS y
  have hker : RingHom.ker ((tq J).appLE ⊤ (tq J ⁻¹ᵁ ⊤) hUST).hom =
      J.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker, hbapp] at hz
      have h1 : Ideal.Quotient.mk J ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom z) = 0 := by
        have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom hz
        have eS2 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).hom.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).inv.hom x) = x :=
          fun x => by rw [← CommRingCat.comp_apply, Iso.inv_hom_id]; rfl
        exact (eS2 _).symm.trans (this.trans (map_zero _))
      rw [← eR' z]
      exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hbapp, eR, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
      rfl
  obtain ⟨hs, hk⟩ := pushout_quot hP hb
  have happ : (pullback.fst p (tq J)).appLE W (pullback.fst p (tq J) ⁻¹ᵁ W) le_rfl =
      (pullback.fst p (tq J)).app W := Scheme.Hom.appLE_eq_app _
  refine ⟨?_, fun x hx => ?_⟩
  · rw [← happ]; exact hs
  · have := hk x (by rw [happ]; exact hx)
    rw [hker, Ideal.map_map] at this
    exact this
end ReciprocityTheory.ChartRestriction.G.DVR.TG
