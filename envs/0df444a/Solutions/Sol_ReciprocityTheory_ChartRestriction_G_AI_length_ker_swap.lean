-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_ker_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:44:04.301261+00:00
-- url     : https://prove2.me/submissions/2d1169ba-75a4-4525-b1a0-4224e854c241

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqOfSurjOfKerEq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_length_eq_of_surj_of_ker_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_mem_ker_lsmul_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
universe u
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {A : Type u} [CommRing A] [IsDomain A] (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  set S : Submodule A (A × A) :=
    LinearMap.ker (b • LinearMap.fst A A A - a • LinearMap.snd A A A) with hSdef
  have hS : ∀ p : A × A, p ∈ S ↔ b * p.1 = a * p.2 := by
    intro p
    rw [hSdef, LinearMap.mem_ker]
    simp [sub_eq_zero]
  have hf0 : ∀ p : S, (Ideal.span {a}).mkQ (p : A × A).1 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) := by
    intro p
    exact (mem_ker_lsmul_mk a b _).mpr ⟨_, (hS _).mp p.2⟩
  have hg0 : ∀ p : S, (Ideal.span {b}).mkQ (p : A × A).2 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a) := by
    intro p
    exact (mem_ker_lsmul_mk b a _).mpr ⟨(p : A × A).1, ((hS _).mp p.2).symm⟩
  let f := LinearMap.codRestrict _
    ((Ideal.span {a}).mkQ ∘ₗ LinearMap.fst A A A ∘ₗ S.subtype) hf0
  let g := LinearMap.codRestrict _
    ((Ideal.span {b}).mkQ ∘ₗ LinearMap.snd A A A ∘ₗ S.subtype) hg0
  apply length_eq_of_surj_of_ker_eq f g
  · rintro ⟨k, hk⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨y, hy⟩ := (mem_ker_lsmul_mk a b x).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hy⟩, rfl⟩
  · rintro ⟨k, hk⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨x, hx⟩ := (mem_ker_lsmul_mk b a y).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hx.symm⟩, rfl⟩
  · ext ⟨⟨x, y⟩, hp⟩
    have hp' := (hS _).mp hp
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.coe_eq_zero, ← Submodule.coe_eq_zero]
    show (Ideal.span {a}).mkQ x = 0 ↔ (Ideal.span {b}).mkQ y = 0
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    simp only at hp'
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      apply mul_left_cancel₀ ha
      rw [← hp']
      ring
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      apply mul_left_cancel₀ hb
      rw [hp']
      ring
end ReciprocityTheory.ChartRestriction.G.AI
