-- Prove2me | solution 1 for P2M_GlobalTheory_SiteCoh_equiv__terminalEquiv_79b4d00cc8cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:52.64842+00:00
-- url     : https://prove2.me/submissions/15f172d4-7fdd-446d-88aa-b328bcfed7d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_SubsingletonOfSubsingletonFreeSheaf
import Theorems.Thm_GlobalTheory_SiteCoh_freeSheafHomEquiv_comp
import Theorems.Thm_P2M_GlobalTheory_SiteCoh_zeroEquiv_mk__3c6a869cada8
import Theorems.Thm_GlobalTheory_SiteCoh_terminalEquiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Opposite Limits Abelian
universe w v u
noncomputable section
open GlobalTheory GlobalTheory.SiteCoh
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]
variable {J}
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
namespace GlobalTheory.SiteCoh
theorem _root_.solution (F : Sheaf J AddCommGrpCat.{v}) {T : C} (hT : IsTerminal T)
    (x : F.H' 0 T) :
    Sheaf.H.equiv₀ F hT (terminalEquiv F 0 hT x) = zeroEquiv F T x := by
  obtain ⟨y, rfl⟩ := (extEquiv F 0 T).symm.surjective x
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  rw [zeroEquiv_mk₀, terminalEquiv_apply, AddEquiv.apply_symm_apply, Ext.mk₀_comp_mk₀]
  obtain ⟨ψ, rfl⟩ : ∃ ψ, (freeSheafIsoConst hT).hom ≫ ψ = φ :=
    ⟨(freeSheafIsoConst hT).inv ≫ φ, by simp⟩
  rw [Iso.inv_hom_id_assoc, freeSheafHomEquiv_comp]
  have h : (Ext.addEquiv₀ (Ext.mk₀.{w} ψ)) = ψ := Ext.addEquiv₀.apply_symm_apply ψ
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, h]
  have h₁ := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J (freePresheafIsoConst hT).hom) (op T))
    (FreeAbelianGroup.of (𝟙 T))
  exact congrArg (ψ.hom.app (op T)) h₁
end GlobalTheory.SiteCoh
