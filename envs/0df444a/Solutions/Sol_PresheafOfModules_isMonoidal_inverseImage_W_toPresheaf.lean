-- Prove2me | solution 1 for PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e5fd97a7-9f56-5861-8370-f5076059e47e

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isSheaf_ihomObj
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"

noncomputable section

namespace PresheafOfModules
p2m_export "PresheafOfModules" "sheafification presheaf sheafificationAdjunction inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms map restrictScalars IsLocallyInjective toPresheaf unit toPresheaf_map_sheafificationAdjunction_unit_app obj IsLocallySurjective isSheaf_ihomObj"
namespace IsMonoidalW
p2m_open "PresheafOfModules"

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
  (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

abbrev PMod := PresheafOfModules.{u} (𝒪 ⋙ forget₂ CommRingCat RingCat)

private abbrev _root_.PresheafOfModules.IsMonoidalW.W : MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))

p2m_export "PresheafOfModules.IsMonoidalW" "W"

abbrev shf : PMod 𝒪 ⥤ SheafOfModules.{u} R := PresheafOfModules.sheafification α

abbrev inc : SheafOfModules.{u} R ⥤ PMod 𝒪 :=
  SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α

abbrev adj : shf 𝒪 R α ⊣ inc 𝒪 R α := PresheafOfModules.sheafificationAdjunction α

scoped instance : (inc 𝒪 R α).Faithful := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.faithful
scoped instance : (inc 𝒪 R α).Full := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.full

lemma W_eq : W (J := J) 𝒪 = (MorphismProperty.isomorphisms _).inverseImage (shf 𝒪 R α) :=
  PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α

lemma isIso_unit_app_of_isSheaf (N : PMod 𝒪) (hN : Presheaf.IsSheaf J N.presheaf) :
    IsIso ((adj 𝒪 R α).unit.app N) := by
  have : IsIso ((PresheafOfModules.toPresheaf _).map ((adj 𝒪 R α).unit.app N)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact isIso_toSheafify J hN
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

lemma isIso_shf_map_unit_whiskerRight (d d' : PMod 𝒪) :
    IsIso ((shf 𝒪 R α).map (((adj 𝒪 R α).unit.app d) ▷ d')) := by
  have h := (Monoidal.Reflective.isIso_tfae (adj 𝒪 R α)).out 0 2
  refine (h.mp ?_) d d'
  intro c d
  apply isIso_unit_app_of_isSheaf
  exact PresheafOfModules.isSheaf_ihomObj _ _ c.isSheaf

include R α in
lemma W_whiskerRight {d₁ d₂ : PMod 𝒪} (g : d₁ ⟶ d₂) (hg : W (J := J) 𝒪 g) (d' : PMod 𝒪) :
    W (J := J) 𝒪 (g ▷ d') := by
  have two3 : (W (J := J) 𝒪).HasTwoOutOfThreeProperty := by
    rw [W_eq 𝒪 R α]; infer_instance
  have hη : ∀ d : PMod 𝒪, W (J := J) 𝒪 ((adj 𝒪 R α).unit.app d ▷ d') := fun d => by
    rw [W_eq 𝒪 R α]
    exact isIso_shf_map_unit_whiskerRight 𝒪 R α d d'
  have hiso : W (J := J) 𝒪 ((inc 𝒪 R α).map ((shf 𝒪 R α).map g) ▷ d') := by
    rw [W_eq 𝒪 R α] at hg ⊢
    simp only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at hg ⊢
    have : IsIso ((inc 𝒪 R α).map ((shf 𝒪 R α).map g)) := Functor.map_isIso _ _
    infer_instance
  have e := (adj 𝒪 R α).unit_naturality g
  have hη₁ := hη d₁
  have hη₂ := hη d₂

  dsimp only [Functor.comp_obj, Functor.id_obj] at e hη₁ hη₂ hiso ⊢
  have h' := (W (J := J) 𝒪).comp_mem _ _ hη₁ hiso
  rw [← comp_whiskerRight, e, comp_whiskerRight] at h'
  exact (W (J := J) 𝒪).of_postcomp _ _ hη₂ h'

end PresheafOfModules.IsMonoidalW
p2m_reactivate "P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.PresheafOfModules P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.PresheafOfModules.IsMonoidalW"
p2m_reactivate "P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.PresheafOfModules"

end
p2m_reactivate "P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.PresheafOfModules P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.PresheafOfModules.IsMonoidalW"

open PresheafOfModules.IsMonoidalW in

theorem solution {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
    (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] :
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))).IsMonoidal where
  whiskerRight g hg d' := W_whiskerRight 𝒪 R α g hg d'
  whiskerLeft d g₁ g₂ g hg :=
    ((W (J := J) 𝒪).arrow_mk_iso_iff (Arrow.isoMk' (g ▷ d) (d ◁ g) (β_ g₁ d) (β_ g₂ d)
      (BraidedCategory.braiding_naturality_left g d).symm)).1 (W_whiskerRight 𝒪 R α g hg d)

end S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
end P2MW
export P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf (solution)
