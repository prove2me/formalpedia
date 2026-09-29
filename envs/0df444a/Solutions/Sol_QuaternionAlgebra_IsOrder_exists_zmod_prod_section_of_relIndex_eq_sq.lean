-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_zmod_prod_section_of_relIndex_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/caa14f1e-9bd1-50b1-a2b0-b620f39a5e4b

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_zmod_prod_section_of_relIndex_eq_sq

set_option autoImplicit false

open QuaternionAlgebra
open scoped Quaternion

namespace B14LQ

theorem natzsmul_eq_ratsmul {a b : ℚ} (ℓ : ℕ) (y : ℍ[ℚ, a, b]) : ((ℓ : ℕ) : ℤ) • y = (ℓ : ℚ) • y := by
  rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]

theorem nonempty_addEquiv_of_natCard_eq_sq (Q : Type) [AddCommGroup Q] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    [Module (ZMod ℓ) Q] [Finite Q] (hQcard : Nat.card Q = ℓ ^ 2) : Nonempty (Q ≃+ (ZMod ℓ × ZMod ℓ)) := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := Q)
  have hrank : Module.finrank (ZMod ℓ) Q = Module.finrank (ZMod ℓ) (ZMod ℓ × ZMod ℓ) := by
    rw [hQcard, Nat.card_zmod] at h1
    rw [Module.finrank_prod, Module.finrank_self]
    exact (Nat.pow_right_injective hℓ.out.two_le h1).symm
  exact ⟨(LinearEquiv.ofFinrankEq _ _ hrank).toAddEquiv⟩

theorem exists_section {G : Type} [AddCommGroup G] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (P L : AddSubgroup G) (hPL : P ≤ L)
    (hLi : L.index = ℓ ^ 2) (hPi : P.index = ℓ ^ 4) (htors : ∀ x : G, x ∈ L → ℓ • x ∈ P) :
    ∃ r : ZMod ℓ × ZMod ℓ → G,
      (∀ v, r v ∈ L) ∧ (∀ v w, r (v + w) - r v - r w ∈ P) ∧ (∀ x : G, x ∈ L → ∃ v, x - r v ∈ P) ∧
      (∀ v w, r v - r w ∈ P → v = w) := by
  classical
  have hQcard : Nat.card (L ⧸ P.addSubgroupOf L) = ℓ ^ 2 := by
    have h := AddSubgroup.relIndex_mul_index hPL
    rw [hLi, hPi, show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hℓ.out.pos 2) h
  have hQtors : ∀ x : L ⧸ P.addSubgroupOf L, ℓ • x = 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
        AddSubmonoidClass.coe_nsmul]
      exact htors _ z.2
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI hfinQ : Finite (L ⧸ P.addSubgroupOf L) :=
    Nat.finite_of_card_ne_zero (by rw [hQcard]; exact pow_ne_zero _ hℓ.out.ne_zero)
  obtain ⟨e⟩ := @nonempty_addEquiv_of_natCard_eq_sq (L ⧸ P.addSubgroupOf L) _ ℓ hℓ
    (AddCommMonoid.zmodModule hQtors) hfinQ hQcard

  obtain ⟨rep, hrep⟩ : ∃ rep : L ⧸ P.addSubgroupOf L → L, ∀ x, QuotientAddGroup.mk (rep x) = x :=
    ⟨fun x => Classical.choose (QuotientAddGroup.mk_surjective x),
      fun x => Classical.choose_spec (QuotientAddGroup.mk_surjective x)⟩
  have hdiff : ∀ z z' : L, (QuotientAddGroup.mk z : L ⧸ P.addSubgroupOf L) = QuotientAddGroup.mk z' ↔
      (z : G) - (z' : G) ∈ P := by
    intro z z'
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]
  refine ⟨fun v => (rep (e.symm v) : G), fun v => (rep (e.symm v)).2, ?_, ?_, ?_⟩
  · intro v w
    have h : (QuotientAddGroup.mk (rep (e.symm (v + w))) : L ⧸ P.addSubgroupOf L) =
        QuotientAddGroup.mk (rep (e.symm v) + rep (e.symm w)) := by
      rw [QuotientAddGroup.mk_add, hrep, hrep, hrep, map_add]
    have := (hdiff _ _).mp h
    rwa [AddSubgroup.coe_add, ← sub_sub] at this
  · intro x hx
    refine ⟨e (QuotientAddGroup.mk ⟨x, hx⟩), ?_⟩
    have h : (QuotientAddGroup.mk (⟨x, hx⟩ : L) : L ⧸ P.addSubgroupOf L) =
        QuotientAddGroup.mk (rep (e.symm (e (QuotientAddGroup.mk ⟨x, hx⟩)))) := by
      rw [hrep, AddEquiv.symm_apply_apply]
    exact (hdiff _ _).mp h
  · intro v w hvw
    have h := (hdiff _ _).mpr hvw
    rw [hrep, hrep] at h
    exact e.symm.injective h

end B14LQ

open B14LQ

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b]) (hL₀ : L₀ ≤ Λ) (hℓL₀ : ∀ x : ↥Λ, (ℓ : ℚ) • (x : ℍ[ℚ, a, b]) ∈ L₀)
    (hL₀_index : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2) :
    ∃ ρ : ZMod ℓ × ZMod ℓ → ↥Λ,
      (∀ v, ((ρ v : ↥Λ) : ℍ[ℚ, a, b]) ∈ L₀) ∧
      (∀ v w, ∃ y : ↥Λ,
        ((ρ (v + w) : ↥Λ) : ℍ[ℚ, a, b]) - (ρ v : ℍ[ℚ, a, b]) - (ρ w : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ x : ↥Λ, (x : ℍ[ℚ, a, b]) ∈ L₀ →
        ∃ v, ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) - (ρ v : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) ∧
      (∀ v w, (∃ y : ↥Λ, ((ρ v : ↥Λ) : ℍ[ℚ, a, b]) - (ρ w : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b])) → v = w) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  have hmemA : ∀ y : ℍ[ℚ, a, b], y ∈ Λ →
      (ℓ : ℤ) • y ∈ Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) :=
    fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  have hmemB : ∀ x : ℍ[ℚ, a, b], x ∈ Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) →
      ∃ y : ↥Λ, x = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro x hx
    have hle : Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) ≤
        Λ.map (DistribSMul.toLinearMap ℤ ℍ[ℚ, a, b] (ℓ : ℤ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp (hle hx)
    refine ⟨⟨y, hy⟩, ?_⟩
    show ((ℓ : ℕ) : ℤ) • y = (ℓ : ℚ) • y
    exact natzsmul_eq_ratsmul ℓ y

  obtain ⟨r, hrL, hradd, hrsurj, hrinj⟩ := exists_section (G := ↥Λ.toAddSubgroup) ℓ
    ((Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup.addSubgroupOf
      Λ.toAddSubgroup)
    (L₀.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup)
    (by
      intro x hx
      rw [AddSubgroup.mem_addSubgroupOf] at hx ⊢
      obtain ⟨y, hy⟩ := hmemB _ hx
      show (x : ℍ[ℚ, a, b]) ∈ L₀
      rw [hy]; exact hℓL₀ y)
    hL₀_index (QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hΛ ℓ hℓ.pos)
    (by
      intro x _
      rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul, ← natCast_zsmul]
      exact hmemA _ x.2)
  refine ⟨fun v => ⟨((r v : ↥Λ.toAddSubgroup) : ℍ[ℚ, a, b]), (r v).2⟩, ?_, ?_, ?_, ?_⟩
  · intro v
    exact (AddSubgroup.mem_addSubgroupOf).mp (hrL v)
  · intro v w
    obtain ⟨y, hy⟩ := hmemB _ ((AddSubgroup.mem_addSubgroupOf).mp (hradd v w))
    exact ⟨y, hy⟩
  · intro x hx
    obtain ⟨v, hv⟩ := hrsurj ⟨(x : ℍ[ℚ, a, b]), x.2⟩ ((AddSubgroup.mem_addSubgroupOf).mpr hx)
    obtain ⟨y, hy⟩ := hmemB _ ((AddSubgroup.mem_addSubgroupOf).mp hv)
    exact ⟨v, y, hy⟩
  · rintro v w ⟨y, hy⟩
    apply hrinj
    rw [AddSubgroup.mem_addSubgroupOf]
    show ((r v : ↥Λ.toAddSubgroup) : ℍ[ℚ, a, b]) - (r w : ℍ[ℚ, a, b]) ∈ _
    rw [hy, ← natzsmul_eq_ratsmul]
    exact hmemA _ y.2

end S_QuaternionAlgebra_IsOrder_exists_zmod_prod_section_of_relIndex_eq_sq
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_zmod_prod_section_of_relIndex_eq_sq (solution)
