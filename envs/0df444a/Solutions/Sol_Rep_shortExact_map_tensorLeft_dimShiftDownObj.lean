-- Prove2me | solution 1 for Rep.shortExact_map_tensorLeft_dimShiftDownObj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/77cafa9a-342b-52a2-aa19-df089a815e35

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift
import Theorems.Thm_Rep_indBotPi_indBotSigma
import Theorems.Thm_Rep_shortExact_map_tensorLeft_indBot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_shortExact_map_tensorLeft_dimShiftDownObj

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep CategoryTheory.MonoidalCategory"

namespace P2mS26F15

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

lemma exact_of_shortExact {T : ShortComplex (Rep.{u} k G)} (hT : T.ShortExact) :
    Function.Exact T.f.hom.toLinearMap T.g.hom.toLinearMap ∧ Function.Injective T.f.hom.toLinearMap
      ∧ Function.Surjective T.g.hom.toLinearMap :=
  ⟨LinearMap.exact_iff.2 ((hT.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker).symm,
    (Rep.mono_iff_injective T.f).1 hT.mono_f, (Rep.epi_iff_surjective T.g).1 hT.epi_g⟩

theorem shortExact_of_retract {S S' : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (i₁ : S'.X₁ →ₗ[k] S.X₁) (i₂ : S'.X₂ →ₗ[k] S.X₂) (i₃ : S'.X₃ →ₗ[k] S.X₃)
    (r₁ : S.X₁ →ₗ[k] S'.X₁) (r₂ : S.X₂ →ₗ[k] S'.X₂) (r₃ : S.X₃ →ₗ[k] S'.X₃)
    (hr₁ : r₁ ∘ₗ i₁ = LinearMap.id) (hr₂ : r₂ ∘ₗ i₂ = LinearMap.id) (hr₃ : r₃ ∘ₗ i₃ = LinearMap.id)
    (hi₁₂ : S.f.hom.toLinearMap ∘ₗ i₁ = i₂ ∘ₗ S'.f.hom.toLinearMap)
    (hi₂₃ : S.g.hom.toLinearMap ∘ₗ i₂ = i₃ ∘ₗ S'.g.hom.toLinearMap)
    (hr₁₂ : S'.f.hom.toLinearMap ∘ₗ r₁ = r₂ ∘ₗ S.f.hom.toLinearMap)
    (hr₂₃ : S'.g.hom.toLinearMap ∘ₗ r₂ = r₃ ∘ₗ S.g.hom.toLinearMap) :
    S'.ShortExact := by
  obtain ⟨ex, inj, surj⟩ := exact_of_shortExact hS
  have hi₁ : Function.Injective i₁ := Function.LeftInverse.injective (g := r₁) fun x => LinearMap.congr_fun hr₁ x
  have inj' : Function.Injective S'.f.hom.toLinearMap := by
    have h : Function.Injective (i₂ ∘ₗ S'.f.hom.toLinearMap) := by
      rw [← hi₁₂]; exact inj.comp hi₁
    exact Function.Injective.of_comp h
  have surj' : Function.Surjective S'.g.hom.toLinearMap := by
    intro y
    obtain ⟨x, hx⟩ := surj (i₃ y)
    refine ⟨r₂ x, ?_⟩
    have e1 := LinearMap.congr_fun hr₂₃ x
    have e3 := LinearMap.congr_fun hr₃ y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e1 e3
    rw [e1, hx, e3]
  have exS : Function.Exact S'.f.hom.toLinearMap S'.g.hom.toLinearMap := by
    intro z
    constructor
    · intro hz
      have h1 : S.g.hom.toLinearMap (i₂ z) = 0 := by
        have := LinearMap.congr_fun hi₂₃ z
        simp only [LinearMap.comp_apply] at this
        rw [this, hz, map_zero]
      obtain ⟨w, hw⟩ := (ex (i₂ z)).1 h1
      refine ⟨r₁ w, ?_⟩
      have e1 := LinearMap.congr_fun hr₁₂ w
      have e2 := LinearMap.congr_fun hr₂ z
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at e1 e2
      rw [e1, hw, e2]
    · rintro ⟨w, rfl⟩
      change (S'.f ≫ S'.g).hom w = 0
      rw [S'.zero]
      rfl
  exact
    { exact := by
        refine (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ ((ShortComplex.moduleCat_exact_iff _).2 ?_)
        intro y hy
        exact (exS y).1 hy
      mono_f := (Rep.mono_iff_injective _).2 inj'
      epi_g := (Rep.epi_iff_surjective _).2 surj' }

def rDown (B : Rep.{u} k G) : (B.indBot : Type u) →ₗ[k] B.dimShiftDownObj :=
  LinearMap.codRestrict (LinearMap.ker (Rep.indBotπ B).hom.toLinearMap)
    (LinearMap.id - B.indBotσ ∘ₗ (Rep.indBotπ B).hom.toLinearMap) (fun x => by
      rw [LinearMap.mem_ker]
      change (Rep.indBotπ B).hom (x - B.indBotσ ((Rep.indBotπ B).hom x)) = 0
      rw [map_sub, Rep.indBotPi_indBotSigma, sub_self])

def ιDown (B : Rep.{u} k G) : (B.dimShiftDownObj : Type u) →ₗ[k] B.indBot :=
  (LinearMap.ker (Rep.indBotπ B).hom.toLinearMap).subtype

lemma rDown_ιDown (B : Rep.{u} k G) : rDown B ∘ₗ ιDown B = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  change (x : B.indBot) - B.indBotσ ((Rep.indBotπ B).hom (x : B.indBot)) = x
  have hx : (Rep.indBotπ B).hom (x : B.indBot) = 0 := x.2
  rw [hx, map_zero, sub_zero]

lemma ιDown_eq (B : Rep.{u} k G) : B.dimShiftDown.f.hom.toLinearMap = ιDown B := rfl

end

end P2mS26F15

open P2mS26F15 in
theorem solution {k G : Type u} [CommRing k] [Group G]
    {X : ShortComplex (Rep.{u} k G)} (A : Rep.{u} k G) (hAX : (X.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    (X.map (MonoidalCategory.tensorLeft A.dimShiftDownObj)).ShortExact := by
  have hS := Rep.shortExact_map_tensorLeft_indBot A hAX
  have wl : ∀ {P Q : Rep.{u} k G} (C : Rep.{u} k G) (φ : P ⟶ Q), (C ◁ φ).hom.toLinearMap = LinearMap.lTensor C φ.hom.toLinearMap :=
    fun C φ => by rw [Rep.hom_whiskerLeft, Representation.IntertwiningMap.toLinearMap_lTensor]
  have hr : ∀ (P : Rep.{u} k G), LinearMap.rTensor P (rDown A) ∘ₗ LinearMap.rTensor P (ιDown A) = LinearMap.id := fun P => by
    rw [← LinearMap.rTensor_comp, rDown_ιDown, LinearMap.rTensor_id]
  refine shortExact_of_retract hS
    (LinearMap.rTensor X.X₁ (ιDown A)) (LinearMap.rTensor X.X₂ (ιDown A)) (LinearMap.rTensor X.X₃ (ιDown A))
    (LinearMap.rTensor X.X₁ (rDown A)) (LinearMap.rTensor X.X₂ (rDown A)) (LinearMap.rTensor X.X₃ (rDown A))
    (hr _) (hr _) (hr _) ?_ ?_ ?_ ?_
  · change (A.indBot ◁ X.f).hom.toLinearMap ∘ₗ _ = _ ∘ₗ (A.dimShiftDownObj ◁ X.f).hom.toLinearMap
    rw [wl, wl, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  · change (A.indBot ◁ X.g).hom.toLinearMap ∘ₗ _ = _ ∘ₗ (A.dimShiftDownObj ◁ X.g).hom.toLinearMap
    rw [wl, wl, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  · change (A.dimShiftDownObj ◁ X.f).hom.toLinearMap ∘ₗ _ = _ ∘ₗ (A.indBot ◁ X.f).hom.toLinearMap
    rw [wl, wl, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  · change (A.dimShiftDownObj ◁ X.g).hom.toLinearMap ∘ₗ _ = _ ∘ₗ (A.indBot ◁ X.g).hom.toLinearMap
    rw [wl, wl, LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

end S_Rep_shortExact_map_tensorLeft_dimShiftDownObj
end P2MW
export P2MW.S_Rep_shortExact_map_tensorLeft_dimShiftDownObj (solution)
