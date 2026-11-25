-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGt_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:23:59.756949+00:00
-- url     : https://prove2.me/submissions/a453d355-ebe3-4045-9719-9c33b3220db5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_transL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_equivL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_normL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_liftNC_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {E : SplitExt S} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂]
set_option maxHeartbeats 800000
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (e : G₁ ≅ G₂) [IsMonHom e.hom] (h : E.IsGt G₁) : E.IsGt G₂ := by
  obtain ⟨d⟩ := h
  have := d.q_hom
  have := d.i_hom
  have : IsIso e.inv.left := ⟨⟨e.hom.left, by rw [← Over.comp_left, e.inv_hom_id, Over.id_left],
    by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]⟩⟩
  have := d.q_flat
  have := d.q_surjective
  have := d.q_affine
  have hact : (lift (fst (splitTorus S E.X) G₂ ≫ d.i ≫ e.hom) (snd _ _) ≫ μ[G₂]).left ≫ e.inv.left =
      (splitTorus S E.X ◁ e.inv).left ≫ (lift (fst (splitTorus S E.X) G₁ ≫ d.i) (snd _ _) ≫ μ[G₁]).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [← Hom.mul_def, ← Hom.mul_def, MonObj.mul_comp, MonObj.comp_mul]
    simp
  have hsnd : (snd (splitTorus S E.X) G₂).left ≫ e.inv.left =
      (splitTorus S E.X ◁ e.inv).left ≫ (snd (splitTorus S E.X) G₁).left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have hfst : (fst (splitTorus S E.X) G₂).left =
      (splitTorus S E.X ◁ e.inv).left ≫ (fst (splitTorus S E.X) G₁).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have he : eSec G₂ ≫ e.inv.left = eSec G₁ := congrArg (fun z => z.left) (IsMonHom.one_hom e.inv)
  have m₁ : ∀ (j : E.ChartIdx) (y : (splitTorus S E.X ⊗ G₂).left),
      y ∈ (snd (splitTorus S E.X) G₂).left ⁻¹ᵁ ((e.inv ≫ d.q).left ⁻¹ᵁ E.chart j) →
      (splitTorus S E.X ◁ e.inv).left y ∈ (snd (splitTorus S E.X) G₁).left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart j) := by
    intro j y hy
    have e₁ := congrArg (fun g => g y) hsnd
    exact (congrArg (fun z => d.q.left z ∈ E.chart j) e₁).mp hy
  have le : ∀ j : E.ChartIdx, (snd (splitTorus S E.X) G₂).left ⁻¹ᵁ ((e.inv ≫ d.q).left ⁻¹ᵁ E.chart j) ≤
      (lift (fst (splitTorus S E.X) G₂ ≫ d.i ≫ e.hom) (snd _ _) ≫ μ[G₂]).left ⁻¹ᵁ
        ((e.inv ≫ d.q).left ⁻¹ᵁ E.chart j) := by
    intro j y hy
    have e₁ := congrArg (fun g => g y) hact
    exact (congrArg (fun z => d.q.left z ∈ E.chart j) e₁).mpr (d.act_le j (m₁ j y hy))
  refine ⟨{ q := e.inv ≫ d.q
            i := d.i ≫ e.hom
            q_hom := inferInstance
            i_hom := inferInstance
            q_flat := by rw [Over.comp_left]; infer_instance
            q_surjective := by rw [Over.comp_left]; infer_instance
            q_affine := by rw [Over.comp_left]; infer_instance
            isKernel := by
              refine IsPullback.of_iso d.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
            u := fun j k => pullU e.inv.left _ (d.u j k)
            coord := fun j V hV hle => ?_
            trans := fun j j' k => transL e.inv.left d.q.left _ _ _ _ _ (d.trans j j' k)
            act_le := le
            equiv := fun j k => equivL _ _ _ _ e.inv.left _ _ _ (d.q.left ⁻¹ᵁ E.chart j) (d.u j k) _ (d.act_le j) _
              (d.equiv j k) hact hsnd hfst (le j) _
            unit_norm := fun j k => normL (eSec G₁) (eSec G₂) e.inv.left he (d.q.left ⁻¹ᵁ E.chart j) _ (d.u j k) _
              (d.unit_norm j k) }⟩
  · have hb : Function.Bijective (e.inv.left.app (d.q.left ⁻¹ᵁ V)).hom :=
      ConcreteCategory.bijective_of_isIso (e.inv.left.app (d.q.left ⁻¹ᵁ V))
    have hl := liftNC_comp (d.q.left.app V).hom (e.inv.left.app (d.q.left ⁻¹ᵁ V)).hom E.basis
      (fun k => res (Scheme.Hom.preimage_mono d.q.left hle) (d.u j k))
      (fun k => res (e.inv.left.preimage_mono (Scheme.Hom.preimage_mono d.q.left hle)) (pullU e.inv.left _ (d.u j k)))
      (fun k => congrArg Units.val (pullU_res₂ e.inv.left (Scheme.Hom.preimage_mono d.q.left hle) (d.u j k)).symm)
    have hb₂ := hb.comp (d.coord j V hV hle)
    rw [← RingHom.coe_comp, ← hl] at hb₂
    exact hb₂
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
