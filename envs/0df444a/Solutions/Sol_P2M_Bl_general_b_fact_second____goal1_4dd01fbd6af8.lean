-- Prove2me | solution 1 for P2M_Bl_general_b_fact_second____goal1_4dd01fbd6af8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:04:44.928833+00:00
-- url     : https://prove2.me/submissions/d66e891b-d247-4623-a0bb-1ad73e5921fb

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1 u_2
namespace Bl.general_b_fact_second'''
private lemma key {O : Type*} {Y : Type*} [CommRing O] [AddCommGroup Y] [Module O Y]
    (R S D E : Submodule O Y) (hD : ∀ y, y ∈ D ↔ y ∈ R ∧ y ∈ S) (hE : E ≤ D) :
    Module.length O (R ⧸ E.comap R.subtype) =
      Module.length O (R ⧸ S.comap R.subtype) + Module.length O (D ⧸ E.comap D.subtype) := by
  have hDR : D ≤ R := fun y hy => ((hD y).1 hy).1
  have hES : E.comap R.subtype ≤ (S.comap R.subtype).comap LinearMap.id :=
    fun x hx => ((hD x).1 (hE hx)).2
  have hEE : E.comap D.subtype ≤ (E.comap R.subtype).comap (Submodule.inclusion hDR) :=
    fun x hx => hx
  let f := Submodule.mapQ (E.comap D.subtype) (E.comap R.subtype) (Submodule.inclusion hDR) hEE
  let g := Submodule.mapQ (E.comap R.subtype) (S.comap R.subtype) LinearMap.id hES
  rw [add_comm]
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · refine (injective_iff_map_eq_zero f).2 ?_
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
    exact hx
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      simp only [g, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      have hyD : (y : Y) ∈ D := (hD y).2 ⟨y.2, hy⟩
      exact ⟨Submodule.Quotient.mk ⟨y, hyD⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      simp only [f, g, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ((hD x).1 x.2).2
end Bl.general_b_fact_second'''
end

set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_second'''
namespace Bl.general_b_fact_second'''
theorem _root_.solution :
  ∀ {O : Type u_1} {Y : Type u_2} [inst : CommRing.{u_1} O] [inst_1 : AddCommGroup.{u_2} Y]
  [inst_2 : Module.{u_1, u_2} O Y] (R S D E : Submodule.{u_1, u_2} O Y),
  (∀ (y : Y),
      Iff (Membership.mem.{u_2, u_2} D y) (And (Membership.mem.{u_2, u_2} R y) (Membership.mem.{u_2, u_2} S y))) →
    LE.le.{u_2} E D →
      Eq.{1}
        (Module.length.{u_1, u_2} O
          (HasQuotient.Quotient.{u_2, u_2} (Subtype.{u_2 + 1} fun (x : Y) ↦ Membership.mem.{u_2, u_2} R x)
            (Submodule.comap.{u_1, u_1, u_2, u_2} (Submodule.subtype.{u_1, u_2} R) E)))
        (HAdd.hAdd.{0, 0, 0}
          (Module.length.{u_1, u_2} O
            (HasQuotient.Quotient.{u_2, u_2} (Subtype.{u_2 + 1} fun (x : Y) ↦ Membership.mem.{u_2, u_2} R x)
              (Submodule.comap.{u_1, u_1, u_2, u_2} (Submodule.subtype.{u_1, u_2} R) S)))
          (Module.length.{u_1, u_2} O
            (HasQuotient.Quotient.{u_2, u_2} (Subtype.{u_2 + 1} fun (x : Y) ↦ Membership.mem.{u_2, u_2} D x)
              (Submodule.comap.{u_1, u_1, u_2, u_2} (Submodule.subtype.{u_1, u_2} D) E)))) := by
  intro O Y _ _ _ R S D E hD hE
  exact key R S D E hD hE
end Bl.general_b_fact_second'''
