-- Prove2me | solution 1 for P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:50.162485+00:00
-- url     : https://prove2.me/submissions/b283fe17-ab75-497d-b8f8-61af8a521c4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe w' v u
open CategoryTheory Limits Abelian Opposite
noncomputable section
open GlobalTheory
open GlobalTheory.SheafLES
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)
namespace GlobalTheory.SheafLES
theorem _root_.solution {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{v})} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ) (U : C) (x : Sheaf.H'.{w'} S₁.X₃ n U) :
    map φ.τ₁ (n + 1) U (δ h₁ n U x) = δ h₂ n U (map φ.τ₃ n U x) := by
  have (y : Ext.{w'} ((freeYoneda J).obj U) S₁.X₃ n) :
      (y.comp h₁.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
        (y.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp h₂.extClass rfl := by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero,
      ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ]
  exact this x
end GlobalTheory.SheafLES
