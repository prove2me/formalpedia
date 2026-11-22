-- Prove2me | solution 1 for TwoCategory.exists_equivalence_iff_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:59:11.133032+00:00
-- url     : https://prove2.me/submissions/0610c02f-21c9-47ea-9251-eff3825e88c1

import Mathlib

open CategoryTheory

set_option autoImplicit false

universe w v u

open Bicategory

namespace Sol_TwoCategory_exists_equivalence_iff_of_iso

/-- One direction: transport an adjoint equivalence along a 2-isomorphism `f ≅ g`. -/
theorem transport {B : Type u} [Bicategory.{w, v} B] {a b : B} {f g : a ⟶ b} (α : f ≅ g) :
    (∃ e : Bicategory.Equivalence a b, e.hom = f) →
      ∃ e : Bicategory.Equivalence a b, e.hom = g := by
  rintro ⟨e, rfl⟩
  exact ⟨Bicategory.Equivalence.mkOfAdjointifyCounit (e.unit ≪≫ whiskerRightIso α e.inv)
    (whiskerLeftIso e.inv α.symm ≪≫ e.counit), rfl⟩

end Sol_TwoCategory_exists_equivalence_iff_of_iso

theorem solution {B : Type u} [Bicategory.{w, v} B] {a b : B}
    {f g : a ⟶ b} (α : f ≅ g) :
    (∃ e : Bicategory.Equivalence a b, e.hom = f) ↔
      (∃ e : Bicategory.Equivalence a b, e.hom = g) :=
  ⟨Sol_TwoCategory_exists_equivalence_iff_of_iso.transport α,
    Sol_TwoCategory_exists_equivalence_iff_of_iso.transport α.symm⟩
