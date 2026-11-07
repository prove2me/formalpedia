-- Prove2me | solution 1 for UAVariety.quot_lift_hom
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T16:55:29.160733+00:00
-- url     : https://prove2.me/submissions/a4b9f24e-f0c9-4958-becb-536d0c45f0bb

import Definitions.Def_UAVariety_defs

universe u₁ v₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace UAVariety

variable {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic]

theorem fu_quot_lift_hom {M : Type*} [L.Structure M] {B : Type*} [L.Structure B]
    (φ : Congruence (L := L) M) (h : M →[L] B) (hφ : ∀ a b, φ.r a b → h a = h b) :
    ∃ g : φ.Quot →[L] B, ∀ a, g (Quotient.mk _ a) = h a := by
  refine ⟨⟨Quotient.lift h hφ, ?_, fun r => isEmptyElim r⟩, fun a => rfl⟩
  intro n f x
  have hx : x = fun i => Quotient.mk φ.toSetoid ((x i).out) :=
    funext fun i => (Quotient.out_eq _).symm
  rw [hx, funMap_quotient_mk']
  show h _ = _
  rw [h.map_fun]; rfl


end UAVariety

theorem solution {L : FirstOrder.Language.{u₁, v₁}} [L.IsAlgebraic] {M : Type*} [L.Structure M] {B : Type*} [L.Structure B]
    (φ : UAVariety.Congruence (L := L) M) (h : M →[L] B) (hφ : ∀ a b, φ.r a b → h a = h b) :
    ∃ g : φ.Quot →[L] B, ∀ a, g (Quotient.mk _ a) = h a :=
  UAVariety.fu_quot_lift_hom φ h hφ
