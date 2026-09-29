-- Prove2me | solution 1 for Rep.natCard_kerModRange_eq_natCard_tate_of_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/f6c9e971-bb63-5917-bfdb-9bd5ae5e049a

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_natCard_kerModRange_eq_natCard_tate_of_addEquiv

set_option autoImplicit false
open CategoryTheory Rep

attribute [local instance 2000] Rep.hV2 Rep.hV1 Submodule.module Representation.Coinvariants.instModule Submodule.Quotient.module

namespace P2mS26G0

variable {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
  {X : Type} [AddCommGroup X] (e : X ≃+ A)
  (d : X →+ X) (hd : ∀ x, e (d x) = A.ρ g (e x) - e x)
  (N : X →+ X) (hN : ∀ x, e (N x) = ∑ i ∈ Finset.range (Nat.card G), A.ρ (g ^ i) (e x))

include hg in

theorem sum_eq_sum_range_pow {M : Type*} [AddCommMonoid M] (f : G → M) :
    ∑ h : G, f h = ∑ i ∈ Finset.range (Nat.card G), f (g ^ i) := by
  classical
  have ho : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [Finset.sum_range]
  symm
  apply Fintype.sum_bijective (fun i : Fin (Nat.card G) => g ^ (i : ℕ))
  · refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, by simp [Nat.card_eq_fintype_card]⟩
    intro i j hij
    apply Fin.ext
    have := pow_inj_mod.1 hij
    rwa [ho, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at this
  · intro i
    rfl

include hg hN in
theorem norm_apply (x : X) : A.ρ.norm (e x) = e (N x) := by
  rw [hN]
  change (∑ h : G, A.ρ h) (e x) = _
  rw [LinearMap.sum_apply]
  exact sum_eq_sum_range_pow g hg fun h => A.ρ h (e x)

omit [Fintype G] in
include hg hd in
theorem mem_ker_iff (x : X) : x ∈ d.ker ↔ e x ∈ A.ρ.invariants := by
  rw [AddMonoidHom.mem_ker, A.ρ.mem_invariants_iff_of_forall_mem_zpowers g hg]
  constructor
  · intro h
    have := hd x
    rw [h, map_zero] at this
    exact (sub_eq_zero.1 this.symm)
  · intro h
    apply e.injective
    rw [hd, h, sub_self, map_zero]

noncomputable def psi : d.ker →+ A.tateH0 :=
  AddMonoidHom.mk' (fun x => (LinearMap.range A.ρ.normBar).mkQ (⟨e x.1, (mem_ker_iff A g hg e d hd x.1).1 x.2⟩ : A.ρ.invariants))
    (fun x y => by
      rw [← map_add]
      exact congrArg _ (Subtype.ext (by simp)))

theorem psi_apply (x : d.ker) :
    psi A g hg e d hd x = (LinearMap.range A.ρ.normBar).mkQ (⟨e x.1, (mem_ker_iff A g hg e d hd x.1).1 x.2⟩ : A.ρ.invariants) := rfl

theorem psi_surjective : Function.Surjective (psi A g hg e d hd) := by
  intro y
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
  refine ⟨⟨e.symm a, (mem_ker_iff A g hg e d hd _).2 (by rw [e.apply_symm_apply]; exact a.2)⟩, ?_⟩
  rw [psi_apply]
  exact congrArg _ (Subtype.ext (e.apply_symm_apply a))

include hN in
theorem ker_psi : (psi A g hg e d hd).ker = N.range.addSubgroupOf d.ker := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, psi_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    LinearMap.mem_range, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ c
    refine ⟨e.symm w, e.injective ?_⟩
    rw [← norm_apply A g hg e N hN, e.apply_symm_apply]
    have := congrArg Subtype.val hc
    rwa [Representation.normBar_mk, Representation.coe_normToInvariants_apply] at this
  · rintro ⟨x', hx'⟩
    refine ⟨Representation.Coinvariants.mk _ (e x'), Subtype.ext ?_⟩
    rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply, norm_apply A g hg e N hN, hx']

include hg hN in
theorem mk_mem_ker_normBar (x : N.ker) : Representation.Coinvariants.mk A.ρ (e x.1) ∈ LinearMap.ker A.ρ.normBar := by
  rw [LinearMap.mem_ker, Representation.normBar_mk]
  apply Subtype.ext
  rw [Representation.coe_normToInvariants_apply, norm_apply A g hg e N hN, (AddMonoidHom.mem_ker).1 x.2, map_zero]
  rfl

noncomputable def chi : N.ker →+ A.tateHneg1 :=
  AddMonoidHom.mk' (fun x => ⟨Representation.Coinvariants.mk A.ρ (e x.1), mk_mem_ker_normBar A g hg e N hN x⟩)
    (fun x y => Subtype.ext (by
      change Representation.Coinvariants.mk A.ρ (e (x.1 + y.1)) =
        Representation.Coinvariants.mk A.ρ (e x.1) + Representation.Coinvariants.mk A.ρ (e y.1)
      rw [map_add, map_add]))

theorem coe_chi_apply (x : N.ker) : (chi A g hg e N hN x : A.ρ.Coinvariants) = Representation.Coinvariants.mk A.ρ (e x.1) := rfl

theorem chi_surjective : Function.Surjective (chi A g hg e N hN) := by
  intro y
  obtain ⟨v, hv⟩ := Representation.Coinvariants.mk_surjective _ (y : A.ρ.Coinvariants)
  have hNv : A.ρ.norm v = 0 := by
    have h := y.2
    rw [LinearMap.mem_ker, ← hv, Representation.normBar_mk] at h
    have := congrArg Subtype.val h
    rwa [Representation.coe_normToInvariants_apply] at this
  refine ⟨⟨e.symm v, (AddMonoidHom.mem_ker).2 (e.injective ?_)⟩, Subtype.ext ?_⟩
  · rw [← norm_apply A g hg e N hN, e.apply_symm_apply, hNv, map_zero]
  · rw [coe_chi_apply, ← hv]
    exact congrArg _ (e.apply_symm_apply v)

include hd in
theorem ker_chi : (chi A g hg e N hN).ker = d.range.addSubgroupOf N.ker := by
  ext x
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
  constructor
  · intro hx
    have h0 : Representation.Coinvariants.mk A.ρ (e x.1) = 0 := by
      have := congrArg Subtype.val hx
      rwa [coe_chi_apply] at this
    rw [Representation.Coinvariants.mk_eq_zero, Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg,
      LinearMap.mem_range] at h0
    obtain ⟨w, hw⟩ := h0
    refine ⟨e.symm w, e.injective ?_⟩
    rw [hd, e.apply_symm_apply, ← hw, LinearMap.sub_apply, LinearMap.id_apply]
  · rintro ⟨x', hx'⟩
    apply Subtype.ext
    rw [coe_chi_apply]
    change Representation.Coinvariants.mk A.ρ (e x.1) = 0
    rw [← hx', Representation.Coinvariants.mk_eq_zero, Representation.FiniteCyclicGroup.coinvariantsKer_eq_range A.ρ g hg,
      LinearMap.mem_range]
    exact ⟨e x', by rw [LinearMap.sub_apply, LinearMap.id_apply, hd]⟩

end P2mS26G0

theorem solution {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    {X : Type} [AddCommGroup X] (e : X ≃+ A)
    (d : X →+ X) (hd : ∀ x, e (d x) = A.ρ g (e x) - e x)
    (N : X →+ X) (hN : ∀ x, e (N x) = ∑ i ∈ Finset.range (Nat.card G), A.ρ (g ^ i) (e x)) :
    Nat.card (↥d.ker ⧸ N.range.addSubgroupOf d.ker) = Nat.card A.tateH0 ∧
      Nat.card (↥N.ker ⧸ d.range.addSubgroupOf N.ker) = Nat.card A.tateHneg1 := by
  constructor
  · rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ (P2mS26G0.psi_surjective A g hg e d hd)).toEquiv,
      P2mS26G0.ker_psi A g hg e d hd N hN]
  · rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _ (P2mS26G0.chi_surjective A g hg e N hN)).toEquiv,
      P2mS26G0.ker_chi A g hg e d hd N hN]

end S_Rep_natCard_kerModRange_eq_natCard_tate_of_addEquiv
end P2MW
export P2MW.S_Rep_natCard_kerModRange_eq_natCard_tate_of_addEquiv (solution)
