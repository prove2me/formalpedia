-- Prove2me | solution 1 for P2M_GlobalTheory_Flasque_subsingleton_H__of_isFlasque_199e9bf4dfbd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:15.787394+00:00
-- url     : https://prove2.me/submissions/835cd6a4-3792-4f7d-ba08-61df33f28df4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Theorems.Thm_GlobalTheory_Flasque_injectiveShortComplex_shortExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
namespace GlobalTheory
namespace Flasque
section Site
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
section Shift
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
end Shift
end Site
section Injective
variable {A : Type u} [Category.{v} A] [Abelian A]
end Injective
section Space
variable {X : TopCat.{u}}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open CategoryTheory Abelian Opposite Limits TopologicalSpace in
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] in
variable {J} in
private lemma freeSheafHomEquiv_comp' (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (h : _root_.GlobalTheory.Flasque.freeSheaf J U ⟶ F) (f : F ⟶ G) :
    _root_.GlobalTheory.Flasque.freeSheafHomEquiv U G (h ≫ f) =
      f.hom.app (op U) (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U F h) := by
  rw [freeSheafHomEquiv_eq_yonedaEquiv, freeSheafHomEquiv_eq_yonedaEquiv,
    Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_right]
  rw [yonedaEquiv_comp]
  rfl
end Space
end Flasque
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {X : TopCat.{u}}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open CategoryTheory Abelian Opposite Limits TopologicalSpace
variable {X : TopCat.{u}}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
namespace GlobalTheory.Flasque
namespace _root_.GlobalTheory.Flasque
theorem _root_.solution (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [hF : F.IsFlasque] (n : ℕ) (U : Opens X) : Subsingleton (F.H' (n + 1) U) := by
  let Y : TopCat.Sheaf AddCommGrpCat.{u} X :=
    _root_.GlobalTheory.Flasque.freeSheaf (Opens.grothendieckTopology X) U
  letI : HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X) := ‹HasExt.{w} (Sheaf _ _)›
  suffices h : ∀ x : Ext.{w} Y F (n + 1), x = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  induction n generalizing F with
  | zero =>
    intro x
    have hS := _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact F
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ Y hS x (Ext.eq_zero_of_injective _) rfl
    obtain ⟨φ, rfl⟩ := Ext.homEquiv₀.symm.surjective x₃
    have hepi := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := U) hS
    rw [AddCommGrpCat.epi_iff_surjective] at hepi
    obtain ⟨t, ht⟩ := hepi (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _ φ)
    let ψ : Y ⟶ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).X₂ :=
      (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _).symm t
    have hψ : ψ ≫ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).g = φ := by
      apply (_root_.GlobalTheory.Flasque.freeSheafHomEquiv U _).injective
      refine (freeSheafHomEquiv_comp' U ψ (_root_.GlobalTheory.Flasque.injectiveShortComplex F).g).trans ?_
      simp only [ψ, AddEquiv.apply_symm_apply]
      exact ht
    rw [Ext.homEquiv₀_symm_apply, ← hψ, ← Ext.mk₀_comp_mk₀,
      Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by simp), hS.comp_extClass, Ext.comp_zero]
  | succ m ih =>
    intro x
    have hS := _root_.GlobalTheory.Flasque.injectiveShortComplex_shortExact F
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ Y hS x (Ext.eq_zero_of_injective _) rfl
    haveI : (_root_.GlobalTheory.Flasque.injectiveShortComplex F).X₃.IsFlasque :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    rw [ih _ x₃, Ext.zero_comp]
end _root_.GlobalTheory.Flasque
end GlobalTheory.Flasque
