-- Prove2me | solution 1 for Rep.nonempty_tate_addEquiv_elementwise
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3d4fab68-7867-5d33-9f0e-a48227090e5f

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_nonempty_tate_addEquiv_elementwise

set_option autoImplicit false
universe u
p2m_open "CategoryTheory Rep P2MW.S_Rep_nonempty_tate_addEquiv_elementwise.Rep"

namespace Rep
p2m_export "Rep" "norm_apply of norm ρ ofMulDistribMulAction tateH0 tateHneg1"
namespace tateElementwiseAux
p2m_open "Rep"

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
  (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (D N : M →* M)
  (hD : ∀ x, D x = g • x / x) (hN : ∀ x, N x = ∏ h : G, h • x)

omit [Fintype G] in
lemma rho_apply (h : G) (w : Rep.ofMulDistribMulAction G M) :
    (Rep.ofMulDistribMulAction G M).ρ h w = Additive.ofMul (h • Additive.toMul (α := M) w) := rfl

omit [Fintype G] in
include hD in

lemma rho_sub_id_apply (w : Rep.ofMulDistribMulAction G M) :
    ((Rep.ofMulDistribMulAction G M).ρ g - LinearMap.id : Rep.ofMulDistribMulAction G M →ₗ[ℤ] Rep.ofMulDistribMulAction G M) w =
      Additive.ofMul (D (Additive.toMul (α := M) w)) := by
  rw [hD, ofMul_div]
  rfl

include hN in

lemma norm_apply (w : Rep.ofMulDistribMulAction G M) :
    (Rep.ofMulDistribMulAction G M).ρ.norm w = Additive.ofMul (N (Additive.toMul (α := M) w)) := by
  rw [hN, ofMul_prod]
  simp only [Representation.norm, LinearMap.coe_sum, Finset.sum_apply, rho_apply]
  rfl

omit [Fintype G] in
lemma eq_one_iff_toAdd_eq_zero {X : Type*} [AddGroup X] (a : Multiplicative X) :
    a = 1 ↔ Multiplicative.toAdd a = 0 := Iff.rfl

omit [Fintype G] in
include hg hD in
lemma ofMul_mem_invariants (x : D.ker) :
    (Additive.ofMul x.1 : Rep.ofMulDistribMulAction G M) ∈ (Rep.ofMulDistribMulAction G M).ρ.invariants := by
  have h1 : D x.1 = 1 := x.2
  rw [hD, div_eq_one] at h1
  exact ((Rep.ofMulDistribMulAction G M).ρ.mem_invariants_iff_of_forall_mem_zpowers g hg _).2
    (congrArg Additive.ofMul h1)

noncomputable def psi : D.ker →* Multiplicative (Rep.ofMulDistribMulAction G M).tateH0 :=
  MonoidHom.mk'
    (fun x => Multiplicative.ofAdd (Submodule.Quotient.mk
      (⟨Additive.ofMul x.1, ofMul_mem_invariants g hg D hD x⟩ : (Rep.ofMulDistribMulAction G M).ρ.invariants)))
    (fun x y => by
      rw [← ofAdd_add, ← Submodule.Quotient.mk_add]
      rfl)

lemma toAdd_psi_apply (x : D.ker) :
    Multiplicative.toAdd (psi g hg D hD x) =
      Submodule.Quotient.mk (⟨Additive.ofMul x.1, ofMul_mem_invariants g hg D hD x⟩ : (Rep.ofMulDistribMulAction G M).ρ.invariants) := rfl

lemma psi_surjective : Function.Surjective (psi g hg D hD) := by
  intro y
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd y)
  have hmem : Additive.toMul a.1 ∈ D.ker := by
    show D _ = 1
    rw [hD, div_eq_one]
    exact congrArg Additive.toMul
      (((Rep.ofMulDistribMulAction G M).ρ.mem_invariants_iff_of_forall_mem_zpowers g hg _).1 a.2)
  refine ⟨⟨Additive.toMul a.1, hmem⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_psi_apply, ← ha]
  rfl

include hN in
lemma ker_psi_eq : (psi g hg D hD).ker = N.range.subgroupOf D.ker := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_range, eq_one_iff_toAdd_eq_zero,
    toAdd_psi_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
    refine ⟨Additive.toMul w, ?_⟩
    have := congrArg Subtype.val hy
    rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply, norm_apply N hN] at this
    exact congrArg Additive.toMul this
  · rintro ⟨m, hm⟩
    refine ⟨Representation.Coinvariants.mk _ (Additive.ofMul m), Subtype.ext ?_⟩
    rw [Representation.normBar_mk, Representation.coe_normToInvariants_apply, norm_apply N hN]
    exact congrArg Additive.ofMul hm

noncomputable def tateH0MulEquiv :
    Multiplicative (Rep.ofMulDistribMulAction G M).tateH0 ≃* D.ker ⧸ N.range.subgroupOf D.ker :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_psi_eq g hg D N hD hN).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (psi_surjective g hg D hD))).symm

include hN in
lemma mk_ofMul_mem_ker_normBar (x : N.ker) :
    Representation.Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ (Additive.ofMul x.1) ∈ LinearMap.ker (Rep.ofMulDistribMulAction G M).ρ.normBar := by
  rw [LinearMap.mem_ker, Representation.normBar_mk]
  refine Subtype.ext ?_
  rw [Representation.coe_normToInvariants_apply, norm_apply N hN]
  have h1 : N x.1 = 1 := x.2
  exact congrArg Additive.ofMul h1

noncomputable def chi : N.ker →* Multiplicative (Rep.ofMulDistribMulAction G M).tateHneg1 :=
  MonoidHom.mk'
    (fun x => Multiplicative.ofAdd
      (⟨Representation.Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ (Additive.ofMul x.1), mk_ofMul_mem_ker_normBar N hN x⟩ :
        (Rep.ofMulDistribMulAction G M).tateHneg1))
    (fun x y => by
      rw [← ofAdd_add]
      exact congrArg Multiplicative.ofAdd (Subtype.ext (by rw [Submodule.coe_add, ← map_add]; rfl)))

lemma coe_toAdd_chi_apply (x : N.ker) :
    ((Multiplicative.toAdd (chi N hN x) : (Rep.ofMulDistribMulAction G M).tateHneg1) : (Rep.ofMulDistribMulAction G M).ρ.Coinvariants) =
      Representation.Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ (Additive.ofMul x.1) := rfl

lemma chi_surjective : Function.Surjective (chi N hN) := by
  intro y
  obtain ⟨v, hv⟩ := Representation.Coinvariants.mk_surjective _
    ((Multiplicative.toAdd y : (Rep.ofMulDistribMulAction G M).tateHneg1) : (Rep.ofMulDistribMulAction G M).ρ.Coinvariants)
  have hNv : (Rep.ofMulDistribMulAction G M).ρ.norm v = 0 := by
    have h := (Multiplicative.toAdd y).2
    rw [LinearMap.mem_ker, ← hv, Representation.normBar_mk] at h
    simpa using congrArg Subtype.val h
  have hmem : Additive.toMul v ∈ N.ker := by
    rw [norm_apply N hN] at hNv
    exact hNv
  refine ⟨⟨Additive.toMul v, hmem⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [coe_toAdd_chi_apply, ← hv]
  rfl

include hg hD in
lemma ker_chi_eq : (chi N hN).ker = D.range.subgroupOf N.ker := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_range, eq_one_iff_toAdd_eq_zero,
    ← Submodule.coe_eq_zero, coe_toAdd_chi_apply, Representation.Coinvariants.mk_eq_zero,
    Representation.FiniteCyclicGroup.coinvariantsKer_eq_range _ g hg, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨Additive.toMul w, congrArg Additive.toMul ((rho_sub_id_apply g D hD w).symm.trans hw)⟩
  · rintro ⟨m, hm⟩
    exact ⟨Additive.ofMul m, (rho_sub_id_apply g D hD _).trans (congrArg Additive.ofMul hm)⟩

noncomputable def tateHneg1MulEquiv :
    Multiplicative (Rep.ofMulDistribMulAction G M).tateHneg1 ≃* N.ker ⧸ D.range.subgroupOf N.ker :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_chi_eq g hg D N hD hN).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (chi_surjective N hN))).symm

end Rep.tateElementwiseAux

open Rep.tateElementwiseAux in
theorem solution
    {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (D N : M →* M)
    (hD : ∀ x, D x = g • x / x) (hN : ∀ x, N x = ∏ h : G, h • x) :
    Nonempty ((Rep.ofMulDistribMulAction G M).tateH0 ≃+ Additive (D.ker ⧸ N.range.subgroupOf D.ker)) ∧
    Nonempty ((Rep.ofMulDistribMulAction G M).tateHneg1 ≃+ Additive (N.ker ⧸ D.range.subgroupOf N.ker)) :=
  ⟨⟨MulEquiv.toAdditiveRight (tateH0MulEquiv g hg D N hD hN)⟩,
   ⟨MulEquiv.toAdditiveRight (tateHneg1MulEquiv g hg D N hD hN)⟩⟩

end S_Rep_nonempty_tate_addEquiv_elementwise
end P2MW
export P2MW.S_Rep_nonempty_tate_addEquiv_elementwise (solution)
