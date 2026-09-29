-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_chain_subgroup_relIndex_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/291b98b0-b5a2-5a3b-887b-12e4c7b29dac

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_relIndex_leftIdeal_mem_of_ne_of_ne
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_submodule_le_mul_mem_relIndex_eq_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_chain_subgroup_relIndex_eq_sq
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.injEq CerednikDrinfeld.QM.mapPt_coe CerednikDrinfeld.QM.FakeEllipticCurve.mk.injEq CerednikDrinfeld.QM.FakeEllipticCurve.mk.sizeOf_spec CerednikDrinfeld.ShimuraCurveModel.ModuliWitness.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver"

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra

namespace P2M
namespace ChainSubgroupRelIndexSq
variable {a b : ℚ}

section Action

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {G : Type*} [CommGroup G] (ρ : ↥Λ → G →* G)
  (hρ_add : ∀ (x y : ↥Λ) (g : G), ρ (x + y) g = ρ x g * ρ y g)
include hρ_add

lemma act_zero (g : G) : ρ 0 g = 1 := by
  have h := hρ_add 0 0 g
  rw [add_zero] at h
  exact left_eq_mul.mp h |>.symm ▸ rfl

lemma act_neg (x : ↥Λ) (g : G) : ρ (-x) g = (ρ x g)⁻¹ := by
  have h := hρ_add (-x) x g
  rw [neg_add_cancel, act_zero ρ hρ_add] at h
  exact eq_inv_of_mul_eq_one_left h.symm

lemma act_nsmul (n : ℕ) (x : ↥Λ) (g : G) : ρ (n • x) g = (ρ x g) ^ n := by
  induction n with
  | zero => simp [act_zero ρ hρ_add]
  | succ n ih => rw [succ_nsmul, hρ_add, ih, pow_succ]

lemma act_zsmul (n : ℤ) (x : ↥Λ) (g : G) : ρ (n • x) g = (ρ x g) ^ n := by
  cases n with
  | ofNat n => simp [act_nsmul ρ hρ_add]
  | negSucc n => rw [negSucc_zsmul, act_neg ρ hρ_add, act_nsmul ρ hρ_add, zpow_negSucc]

def orbit (g : G) : ↥Λ.toAddSubgroup →+ Additive G where
  toFun x := Additive.ofMul (ρ ⟨x.1, x.2⟩ g)
  map_zero' := by
    change Additive.ofMul (ρ 0 g) = 0
    rw [act_zero ρ hρ_add]; rfl
  map_add' x y := by
    change Additive.ofMul (ρ (⟨x.1, x.2⟩ + ⟨y.1, y.2⟩) g) = _
    rw [hρ_add]; rfl

lemma orbit_apply (g : G) (x : ↥Λ.toAddSubgroup) :
    orbit ρ hρ_add g x = Additive.ofMul (ρ ⟨x.1, x.2⟩ g) := rfl

def kerSub (g : G) : Submodule ℤ ℍ[ℚ, a, b] :=
  ((orbit ρ hρ_add g).ker.map Λ.toAddSubgroup.subtype).toIntSubmodule

lemma mem_kerSub (g : G) (x : ℍ[ℚ, a, b]) :
    x ∈ kerSub ρ hρ_add g ↔ ∃ hx : x ∈ Λ, ρ ⟨x, hx⟩ g = 1 := by
  unfold kerSub
  rw [← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule, SetLike.mem_coe, AddSubgroup.mem_map]
  simp only [AddMonoidHom.mem_ker, AddSubgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa [orbit_apply] using hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, by simpa [orbit_apply] using h, rfl⟩

lemma kerSub_le (g : G) : kerSub ρ hρ_add g ≤ Λ := fun x hx =>
  ((mem_kerSub ρ hρ_add g x).1 hx).1

lemma relIndex_kerSub (g : G) :
    (kerSub ρ hρ_add g).toAddSubgroup.relIndex Λ.toAddSubgroup =
      Nat.card (orbit ρ hρ_add g).range := by
  have h1 : (kerSub ρ hρ_add g).toAddSubgroup =
      (orbit ρ hρ_add g).ker.map Λ.toAddSubgroup.subtype := by
    unfold kerSub; simp
  rw [h1, ← AddSubgroup.index_ker]
  have := AddSubgroup.relIndex_comap ((orbit ρ hρ_add g).ker.map Λ.toAddSubgroup.subtype)
    Λ.toAddSubgroup.subtype ⊤
  rw [AddSubgroup.comap_map_eq_self_of_injective (Λ.toAddSubgroup.subtype_injective),
    AddSubgroup.relIndex_top_right, ← AddMonoidHom.range_eq_map,
    AddSubgroup.range_subtype] at this
  exact this.symm

end Action

section Orbit

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {G : Type*} [CommGroup G] (ρ : ↥Λ → G →* G)
  (hρ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h1⟩ = MonoidHom.id G)
  (hρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
  (hρ_add : ∀ (x y : ↥Λ) (g : G), ρ (x + y) g = ρ x g * ρ y g)

def IsStable (H : Subgroup G) : Prop := ∀ (x : ↥Λ) (g : G), g ∈ H → ρ x g ∈ H

def subRange (L : Submodule ℤ ℍ[ℚ, a, b]) (g : G) : Subgroup G :=
  AddSubgroup.toSubgroup'
    ((L.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup).map (orbit ρ hρ_add g))

lemma mem_subRange (L : Submodule ℤ ℍ[ℚ, a, b]) (g h : G) :
    h ∈ subRange ρ hρ_add L g ↔ ∃ (x : ℍ[ℚ, a, b]) (hx : x ∈ Λ), x ∈ L ∧ ρ ⟨x, hx⟩ g = h := by
  unfold subRange
  rw [AddSubgroup.mem_toSubgroup', AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyh⟩
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    exact ⟨y.1, y.2, hy, by simpa [orbit_apply] using hyh⟩
  · rintro ⟨x, hx, hxL, hxh⟩
    refine ⟨⟨x, hx⟩, ?_, ?_⟩
    · rw [AddSubgroup.mem_addSubgroupOf]; exact hxL
    · simpa [orbit_apply] using hxh

lemma mem_subRange_top (g h : G) :
    h ∈ subRange ρ hρ_add Λ g ↔ ∃ x : ↥Λ, ρ x g = h := by
  rw [mem_subRange]
  constructor
  · rintro ⟨x, hx, -, hxh⟩; exact ⟨⟨x, hx⟩, hxh⟩
  · rintro ⟨x, hxh⟩; exact ⟨x.1, x.2, x.2, hxh⟩

lemma card_subRange_top (g : G) :
    Nat.card (subRange ρ hρ_add Λ g) =
      (kerSub ρ hρ_add g).toAddSubgroup.relIndex Λ.toAddSubgroup := by
  rw [relIndex_kerSub]
  refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun h => ?_)
  rw [mem_subRange_top, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨x, hxh⟩; exact ⟨⟨x.1, x.2⟩, by simp [orbit_apply, hxh]⟩
  · rintro ⟨x, hxh⟩; exact ⟨⟨x.1, x.2⟩, by simpa [orbit_apply] using hxh⟩

include hρ_mul in
lemma subRange_stable (hΛo : IsOrder Λ) (L : Submodule ℤ ℍ[ℚ, a, b])
    (hleft : ∀ m ∈ Λ, ∀ x ∈ L, m * x ∈ L) (g : G) :
    IsStable ρ (subRange ρ hρ_add L g) := by
  intro y h hh
  rw [mem_subRange] at hh ⊢
  obtain ⟨x, hx, hxL, rfl⟩ := hh
  refine ⟨(y : ℍ[ℚ, a, b]) * x, hΛo.mul_mem y.2 hx, hleft _ y.2 _ hxL, ?_⟩
  have := hρ_mul y ⟨x, hx⟩ (hΛo.mul_mem y.2 hx)
  simp only at this
  rw [this]; rfl

lemma subRange_le (L : Submodule ℤ ℍ[ℚ, a, b]) {M : Subgroup G}
    (hM : IsStable ρ M) {g : G} (hg : g ∈ M) : subRange ρ hρ_add L g ≤ M := by
  intro h hh
  rw [mem_subRange] at hh
  obtain ⟨x, hx, -, rfl⟩ := hh
  exact hM _ _ hg

include hρ_one in
lemma self_mem_subRange (L : Submodule ℤ ℍ[ℚ, a, b]) (h1 : (1 : ℍ[ℚ, a, b]) ∈ L)
    (h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ) (g : G) : g ∈ subRange ρ hρ_add L g :=
  (mem_subRange ρ hρ_add L g g).2 ⟨1, h1Λ, h1, by rw [hρ_one h1Λ]; rfl⟩

lemma le_kerSub_of_subRange_eq_bot (L : Submodule ℤ ℍ[ℚ, a, b]) (hL : L ≤ Λ) (g : G)
    (h : subRange ρ hρ_add L g = ⊥) : L ≤ kerSub ρ hρ_add g := by
  intro x hxL
  rw [mem_kerSub]
  refine ⟨hL hxL, ?_⟩
  have : ρ ⟨x, hL hxL⟩ g ∈ subRange ρ hρ_add L g :=
    (mem_subRange ρ hρ_add L g _).2 ⟨x, hL hxL, hxL, rfl⟩
  rwa [h, Subgroup.mem_bot] at this

include hρ_one in
lemma one_mem_of_self_mem_subRange (L : Submodule ℤ ℍ[ℚ, a, b])
    (h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ) (g : G) (hker : kerSub ρ hρ_add g ≤ L)
    (hg : g ∈ subRange ρ hρ_add L g) : (1 : ℍ[ℚ, a, b]) ∈ L := by
  rw [mem_subRange] at hg
  obtain ⟨x, hx, hxL, hxg⟩ := hg
  have hker1 : (1 : ℍ[ℚ, a, b]) - x ∈ kerSub ρ hρ_add g := by
    rw [mem_kerSub]
    refine ⟨sub_mem h1Λ hx, ?_⟩
    have hsub : (⟨1 - x, sub_mem h1Λ hx⟩ : ↥Λ) = ⟨1, h1Λ⟩ + -⟨x, hx⟩ := by
      apply Subtype.ext; simp [sub_eq_add_neg]
    rw [hsub, hρ_add, act_neg ρ hρ_add, hxg, hρ_one h1Λ, MonoidHom.id_apply, mul_inv_cancel]
  have := L.add_mem (hker hker1) hxL
  simpa using this

include hρ_one in
lemma one_notMem_kerSub {g : G} (hg : g ≠ 1) :
    (1 : ℍ[ℚ, a, b]) ∉ kerSub ρ hρ_add g := by
  rw [mem_kerSub]
  rintro ⟨h1, h⟩
  rw [hρ_one h1, MonoidHom.id_apply] at h
  exact hg h

include hρ_mul in
lemma kerSub_left (hΛo : IsOrder Λ) (g : G) :
    ∀ m ∈ Λ, ∀ x ∈ kerSub ρ hρ_add g, m * x ∈ kerSub ρ hρ_add g := by
  intro m hm x hx
  rw [mem_kerSub] at hx ⊢
  obtain ⟨hx, hxg⟩ := hx
  refine ⟨hΛo.mul_mem hm hx, ?_⟩
  have := hρ_mul ⟨m, hm⟩ ⟨x, hx⟩ (hΛo.mul_mem hm hx)
  simp only at this
  rw [this, MonoidHom.comp_apply, hxg, map_one]

lemma smul_mem_kerSub {M : Subgroup G} (hM : IsStable ρ M) {ℓ : ℕ}
    (hℓM : ∀ h ∈ M, h ^ ℓ = 1) {g : G} (hg : g ∈ M) :
    ∀ y ∈ Λ, ((ℓ : ℕ) : ℤ) • y ∈ kerSub ρ hρ_add g := by
  intro y hy
  rw [mem_kerSub]
  refine ⟨Λ.smul_mem _ hy, ?_⟩
  have : (⟨((ℓ : ℕ) : ℤ) • y, Λ.smul_mem _ hy⟩ : ↥Λ) = ((ℓ : ℕ) : ℤ) • ⟨y, hy⟩ := rfl
  rw [this, act_zsmul ρ hρ_add, zpow_natCast]
  exact hℓM _ (hM _ _ hg)

lemma le_of_one_mem (L : Submodule ℤ ℍ[ℚ, a, b]) (hleft : ∀ m ∈ Λ, ∀ x ∈ L, m * x ∈ L)
    (h1 : (1 : ℍ[ℚ, a, b]) ∈ L) : Λ ≤ L := fun m hm => by
  simpa using hleft m hm 1 h1

end Orbit

section Lattice

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]}

abbrev ellSpan (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) : Submodule ℤ ℍ[ℚ, a, b] :=
  Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))

lemma ellSpan_eq_map (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) :
    ellSpan Λ ℓ = Λ.map (DistribSMul.toLinearMap ℤ ℍ[ℚ, a, b] (ℓ : ℤ)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

lemma mem_ellSpan (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) (x : ℍ[ℚ, a, b]) :
    x ∈ ellSpan Λ ℓ ↔ ∃ y ∈ Λ, x = (ℓ : ℤ) • y := by
  rw [ellSpan_eq_map, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

lemma ellSpan_le_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) (J : Submodule ℤ ℍ[ℚ, a, b]) :
    ellSpan Λ ℓ ≤ J ↔ ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J := by
  rw [Submodule.span_le, Set.image_subset_iff]
  rfl

lemma eq_ellSpan_of_forall_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ)
    (L : Submodule ℤ ℍ[ℚ, a, b]) (h : ∀ x, x ∈ L ↔ ∃ y ∈ Λ, x = (ℓ : ℤ) • y) :
    L = ellSpan Λ ℓ := by
  ext x; rw [h, mem_ellSpan]

lemma natCast_smul_eq_zsmul (ℓ : ℕ) (x : ℍ[ℚ, a, b]) : (ℓ : ℚ) • x = (ℓ : ℤ) • x := by
  rw [← Int.cast_smul_eq_zsmul ℚ (ℓ : ℤ) x, Int.cast_natCast]

end Lattice

section Key

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
  {Λ : Submodule ℤ ℍ[ℚ, a, b]} {G : Type*} [CommGroup G] (ρ : ↥Λ → G →* G)
  (hρ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h1⟩ = MonoidHom.id G)
  (hρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
  (hρ_add : ∀ (x y : ↥Λ) (g : G), ρ (x + y) g = ρ x g * ρ y g)

lemma exists_prime_forall_pow_eq_one {M : Subgroup G} (hMfin : (M : Set G).Finite)
    (hMne : M ≠ ⊥) (hM : IsStable ρ M)
    (hmin : ∀ H : Subgroup G, IsStable ρ H → H ≤ M → H = ⊥ ∨ H = M) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ∀ g ∈ M, g ^ ℓ = 1 := by
  haveI : Finite M := Set.finite_coe_iff.mpr hMfin
  have h1 : 1 < Nat.card M := M.one_lt_card_iff_ne_bot.2 hMne
  obtain ⟨ℓ, hℓ, hℓdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt h1)
  haveI := Fact.mk hℓ
  obtain ⟨g₁, hg₁⟩ := exists_prime_orderOf_dvd_card' (G := M) ℓ hℓdvd
  obtain ⟨Mℓ, hMℓ⟩ : ∃ Mℓ : Subgroup G, ∀ g, g ∈ Mℓ ↔ g ∈ M ∧ g ^ ℓ = 1 :=
    ⟨M ⊓ (powMonoidHom ℓ : G →* G).ker, fun g => by
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, powMonoidHom_apply]⟩
  have hMℓ_stable : IsStable ρ Mℓ := by
    intro x g hg
    rw [hMℓ] at hg ⊢
    refine ⟨hM _ _ hg.1, ?_⟩
    rw [← map_pow, hg.2, map_one]
  have hMℓ_le : Mℓ ≤ M := fun g hg => ((hMℓ g).1 hg).1
  refine ⟨ℓ, hℓ, ?_⟩
  rcases hmin Mℓ hMℓ_stable hMℓ_le with h | h
  · exfalso
    have hg₁mem : (g₁ : G) ∈ Mℓ := by
      rw [hMℓ]
      refine ⟨g₁.2, ?_⟩
      have := pow_orderOf_eq_one g₁
      rw [hg₁] at this
      exact_mod_cast congrArg Subtype.val this
    rw [h, Subgroup.mem_bot] at hg₁mem
    have : orderOf g₁ = 1 := by
      rw [orderOf_eq_one_iff]; exact Subtype.ext hg₁mem
    rw [hg₁] at this
    exact hℓ.one_lt.ne' this
  · intro g hg
    have : g ∈ Mℓ := h ▸ hg
    exact ((hMℓ g).1 this).2

include hρ_one hρ_mul in

lemma relIndex_kerSub_eq_sq (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (hΛ : IsMaximalOrder Λ) {M : Subgroup G} (hM : IsStable ρ M)
    (hmin : ∀ H : Subgroup G, IsStable ρ H → H ≤ M → H = ⊥ ∨ H = M)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ∀ h ∈ M, h ^ ℓ = 1) {g : G} (hg : g ∈ M) (hg1 : g ≠ 1) :
    (kerSub ρ hρ_add g).toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧
    ((ℓ = q ∨ ℓ = q') →
      ∀ x, x ∈ kerSub ρ hρ_add g ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (ℓ : ℚ) * n) := by
  have hΛo : IsOrder Λ := hΛ.1
  set J := kerSub ρ hρ_add g with hJdef
  have hJΛ : J ≤ Λ := kerSub_le ρ hρ_add g
  have hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J := smul_mem_kerSub ρ hρ_add hM hℓM hg
  have hJleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := kerSub_left ρ hρ_mul hρ_add hΛo g
  have h1J : (1 : ℍ[ℚ, a, b]) ∉ J := one_notMem_kerSub ρ hρ_one hρ_add hg1
  have hsq_ne_one : ℓ ^ 2 ≠ 1 := (Nat.one_lt_pow two_ne_zero hℓ.one_lt).ne'
  have hfour_ne_sq : ℓ ^ 4 ≠ ℓ ^ 2 := fun h =>
    absurd (Nat.pow_right_injective hℓ.two_le h) (by decide)
  have hJne : J.toAddSubgroup.relIndex Λ.toAddSubgroup ≠ 1 := by
    rw [Ne, AddSubgroup.relIndex_eq_one]
    intro h
    exact h1J (h hΛo.one_mem)

  obtain ⟨L₀, hL₀Λ, hℓL₀, hL₀left, hL₀idx⟩ :=
    IsMaximalOrder.exists_submodule_le_mul_mem_relIndex_eq_sq hqq' hB Λ hΛ ℓ hℓ
  have hℓL₀' : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ L₀ := fun y hy => by
    simpa [natCast_smul_eq_zsmul] using hℓL₀ ⟨y, hy⟩
  have hL₀left' : ∀ m ∈ Λ, ∀ x ∈ L₀, m * x ∈ L₀ := fun m hm x hx => hL₀left ⟨m, hm⟩ x hx
  have hL₀stab := subRange_stable ρ hρ_mul hρ_add hΛo L₀ hL₀left' g
  have hL₀le : subRange ρ hρ_add L₀ g ≤ M := subRange_le ρ hρ_add L₀ hM hg

  have hL₀J : J ≤ L₀ → L₀ = J := fun hJL₀ => by
    rcases hmin _ hL₀stab hL₀le with h | h
    · exact le_antisymm (le_kerSub_of_subRange_eq_bot ρ hρ_add L₀ hL₀Λ g h) hJL₀
    · exfalso
      have h1 : (1 : ℍ[ℚ, a, b]) ∈ L₀ :=
        one_mem_of_self_mem_subRange ρ hρ_one hρ_add L₀ hΛo.one_mem g hJL₀ (h ▸ hg)
      have hle : Λ ≤ L₀ := le_of_one_mem L₀ hL₀left' h1
      have : L₀.toAddSubgroup.relIndex Λ.toAddSubgroup = 1 :=
        AddSubgroup.relIndex_eq_one.2 (Submodule.toAddSubgroup_mono hle)
      rw [hL₀idx] at this
      exact hsq_ne_one this

  have hS4 : (ellSpan Λ ℓ).toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 4 :=
    IsOrder.relIndex_span_smul_eq_pow_four hΛo ℓ hℓ.pos
  have hSJ : ellSpan Λ ℓ ≤ J := (ellSpan_le_iff Λ ℓ J).2 hℓJ
  have hSL₀ : ellSpan Λ ℓ ≤ L₀ := (ellSpan_le_iff Λ ℓ L₀).2 hℓL₀'
  have hmul : (ellSpan Λ ℓ).toAddSubgroup.relIndex J.toAddSubgroup *
      J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 4 := by
    rw [AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hSJ)
      (Submodule.toAddSubgroup_mono hJΛ), hS4]
  by_cases hram : ℓ = q ∨ ℓ = q'
  ·
    obtain ⟨⟨-, -, ⟨x₁, hx₁Λ, hx₁P, hx₁nS⟩, -, -⟩, htri⟩ :=
      IsMaximalOrder.leftIdeal_eq_or_eq_or_eq_of_isIndefiniteRamifiedExactlyAt_of_eq_or_eq
        hB Λ hΛ ℓ hram
    have hL₀P : ∀ x, x ∈ L₀ ↔ x ∈ Λ ∧ ∃ n : ℤ, nrd x = (ℓ : ℚ) * n := by
      rcases htri L₀ hL₀Λ hℓL₀' hL₀left' with h | h | h
      · exfalso
        have := eq_ellSpan_of_forall_iff Λ ℓ L₀ h
        rw [this, hS4] at hL₀idx
        exact hfour_ne_sq hL₀idx
      · exact h
      · exfalso
        rw [h, AddSubgroup.relIndex_self] at hL₀idx
        exact hsq_ne_one hL₀idx.symm
    rcases htri J hJΛ hℓJ hJleft with h | h | h
    · exfalso
      have hJL₀ : J ≤ L₀ := fun x hx => by
        obtain ⟨y, hy, rfl⟩ := (h x).1 hx
        exact hℓL₀' y hy
      have hL₀eq := hL₀J hJL₀
      have hx₁J : x₁ ∈ J := hL₀eq ▸ (hL₀P x₁).2 ⟨hx₁Λ, hx₁P⟩
      exact hx₁nS ((h x₁).1 hx₁J)
    · refine ⟨?_, fun _ => h⟩
      have : J = L₀ := by
        ext x; rw [h, hL₀P]
      rw [this]
      exact hL₀idx
    · exfalso
      exact h1J (h ▸ hΛo.one_mem)
  ·
    have hℓq : ℓ ≠ q := fun h => hram (Or.inl h)
    have hℓq' : ℓ ≠ q' := fun h => hram (Or.inr h)
    haveI := Fact.mk hℓ
    have hT2 := IsMaximalOrder.relIndex_leftIdeal_mem_of_ne_of_ne hB Λ hΛ ℓ hℓq hℓq' J hJΛ hℓJ hJleft
    refine ⟨?_, fun h => absurd h hram⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT2
    rcases hT2 with h | h | h
    · exfalso
      have hJS : J ≤ ellSpan Λ ℓ := by
        have := AddSubgroup.relIndex_eq_one.1 h
        exact fun x hx => this hx
      have hJeq : J = ellSpan Λ ℓ := le_antisymm hJS hSJ
      have hL₀eq := hL₀J (hJeq ▸ hSL₀)
      rw [hL₀eq, hJeq, hS4] at hL₀idx
      exact hfour_ne_sq hL₀idx
    · rw [h, show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring] at hmul
      exact mul_left_cancel₀ (pow_ne_zero 2 hℓ.ne_zero) hmul
    · exfalso
      rw [h] at hmul
      exact hJne (mul_left_cancel₀ (pow_ne_zero 4 hℓ.ne_zero) (hmul.trans (mul_one _).symm))

include hρ_one hρ_mul hρ_add in

lemma key (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (hΛ : IsMaximalOrder Λ) {M : Subgroup G} (hMfin : (M : Set G).Finite) (hMne : M ≠ ⊥)
    (hM : IsStable ρ M)
    (hmin : ∀ H : Subgroup G, IsStable ρ H → H ≤ M → H = ⊥ ∨ H = M) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ Nat.card M = ℓ ^ 2 ∧ (∀ g ∈ M, g ^ ℓ = 1) ∧
      ((ℓ = q ∨ ℓ = q') → ∀ g ∈ M, ∀ (m : ↥Λ) (k : ℤ),
        (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((ℓ : ℤ) * k : ℚ) : ℍ[ℚ, a, b]) →
          ρ m g = 1) := by
  have hΛo : IsOrder Λ := hΛ.1
  obtain ⟨ℓ, hℓ, hℓM⟩ := exists_prime_forall_pow_eq_one ρ hMfin hMne hM hmin
  refine ⟨ℓ, hℓ, ?_, hℓM, ?_⟩
  ·
    obtain ⟨g₀, hg₀M, hg₀⟩ : ∃ g₀ ∈ M, g₀ ≠ 1 := by
      by_contra! h
      exact hMne ((Subgroup.eq_bot_iff_forall M).2 h)
    have hst : IsStable ρ (subRange ρ hρ_add Λ g₀) :=
      subRange_stable ρ hρ_mul hρ_add hΛo Λ (fun m hm x hx => hΛo.mul_mem hm hx) g₀
    have hle : subRange ρ hρ_add Λ g₀ ≤ M := subRange_le ρ hρ_add Λ hM hg₀M
    have hg₀mem : g₀ ∈ subRange ρ hρ_add Λ g₀ :=
      self_mem_subRange ρ hρ_one hρ_add Λ hΛo.one_mem hΛo.one_mem g₀
    rcases hmin _ hst hle with h | h
    · exfalso
      rw [h, Subgroup.mem_bot] at hg₀mem
      exact hg₀ hg₀mem
    · rw [← h, card_subRange_top]
      exact (relIndex_kerSub_eq_sq ρ hρ_one hρ_mul hρ_add hqq' hB hΛ hM hmin hℓ hℓM hg₀M hg₀).1
  · intro hram g hg m k hmk
    by_cases hg1 : g = 1
    · rw [hg1, map_one]
    have hP := (relIndex_kerSub_eq_sq ρ hρ_one hρ_mul hρ_add hqq' hB hΛ hM hmin hℓ hℓM hg hg1).2
      hram (m : ℍ[ℚ, a, b])
    have hnrd : nrd (m : ℍ[ℚ, a, b]) = (ℓ : ℚ) * k := by
      rw [mul_star_eq_coe_nrd] at hmk
      have := QuaternionAlgebra.coe_injective hmk
      rw [this]; push_cast; ring
    obtain ⟨hm, hmg⟩ := (mem_kerSub ρ hρ_add g _).1 (hP.2 ⟨m.2, k, hnrd⟩)
    exact hmg

end Key

section Main

universe u

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]

def Goal (q q' : ℕ) (Λ : Submodule ℤ ℍ[ℚ, a, b]) {G : Type u} [CommGroup G] (ρ : ↥Λ → G →* G)
    (N : Subgroup G) : Prop :=
  ∃ (e : ℕ) (ℓ : Fin e → ℕ) (H : Fin (e + 1) → Subgroup G),
      (∀ j, (ℓ j).Prime) ∧ H 0 = ⊥ ∧ H (Fin.last e) = N ∧
      (∀ j : Fin e, H j.castSucc ≤ H j.succ) ∧
      (∀ (j : Fin (e + 1)) (x : ↥Λ) (g : G), g ∈ H j → ρ x g ∈ H j) ∧
      (∀ j : Fin e, (H j.castSucc).relIndex (H j.succ) = ℓ j ^ 2) ∧
      (∀ (j : Fin e) (g : G), g ∈ H j.succ → g ^ (ℓ j) ∈ H j.castSucc) ∧
      (∀ j : Fin e, (ℓ j = q ∨ ℓ j = q') → ∀ g : G, g ∈ H j.succ →
        ∀ (m : ↥Λ) (k : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((ℓ j : ℤ) * k : ℚ) : ℍ[ℚ, a, b]) →
          ρ m g ∈ H j.castSucc) ∧
      Nat.card N = ∏ j, ℓ j ^ 2

omit [Fact q.Prime] [Fact q'.Prime] in
lemma goal_bot (Λ : Submodule ℤ ℍ[ℚ, a, b]) {G : Type u} [CommGroup G] (ρ : ↥Λ → G →* G) :
    Goal q q' Λ ρ (⊥ : Subgroup G) := by
  refine ⟨0, Fin.elim0, fun _ => ⊥, fun j => j.elim0, rfl, rfl, fun j => j.elim0, ?_,
    fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, ?_⟩
  · intro j x g hg
    rw [Subgroup.mem_bot] at hg ⊢
    rw [hg, map_one]
  · rw [Subgroup.card_bot, Fin.prod_univ_zero]

theorem main (hqq' : q' ≠ q) (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (n : ℕ) :
    ∀ {G : Type u} [CommGroup G] (ρ : ↥Λ → G →* G)
      (_hρ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h1⟩ = MonoidHom.id G)
      (_hρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
      (_hρ_add : ∀ (x y : ↥Λ) (g : G), ρ (x + y) g = ρ x g * ρ y g)
      (N : Subgroup G) (_hN : (N : Set G).Finite)
      (_hstab : ∀ (x : ↥Λ) (g : G), g ∈ N → ρ x g ∈ N),
      Nat.card N = n → Goal q q' Λ ρ N := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ ρ hρ_one hρ_mul hρ_add N hN hstab hcard
  classical
  by_cases hNbot : N = ⊥
  · rw [hNbot]; exact goal_bot Λ ρ
  haveI hNfin : Finite N := Set.finite_coe_iff.mpr hN

  have hex : ∃ k, ∃ M : Subgroup G, M ≤ N ∧ M ≠ ⊥ ∧ IsStable ρ M ∧ Nat.card M = k :=
    ⟨_, N, le_rfl, hNbot, hstab, rfl⟩
  obtain ⟨M, hMN, hMne, hMst, hMcard⟩ := Nat.find_spec hex
  have hMfin : (M : Set G).Finite := hN.subset hMN
  haveI : Finite M := Set.finite_coe_iff.mpr hMfin
  have hmin : ∀ H : Subgroup G, IsStable ρ H → H ≤ M → H = ⊥ ∨ H = M := by
    intro H hH hHM
    by_cases hH0 : H = ⊥
    · exact Or.inl hH0
    right
    have hk : Nat.find hex ≤ Nat.card H := Nat.find_min' hex ⟨H, hHM.trans hMN, hH0, hH, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hHM (hMcard ▸ hk)
  obtain ⟨ℓ₀, hℓ₀, hcardM, hpowM, hramM⟩ :=
    key ρ hρ_one hρ_mul hρ_add hqq' hB hΛ hMfin hMne hMst hmin

  haveI : M.Normal := inferInstance
  let π : G →* G ⧸ M := QuotientGroup.mk' M
  have hπker : π.ker = M := QuotientGroup.ker_mk' M
  let ρ' : ↥Λ → (G ⧸ M) →* (G ⧸ M) := fun x =>
    QuotientGroup.map M M (ρ x) (fun g hg => Subgroup.mem_comap.2 (hMst x g hg))
  have hρ'π : ∀ (x : ↥Λ) (g : G), ρ' x (π g) = π (ρ x g) := fun x g => rfl
  have hρ'_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ' ⟨1, h1⟩ = MonoidHom.id _ := by
    intro h1
    refine QuotientGroup.monoidHom_ext M ?_
    ext g
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [show QuotientGroup.mk' M g = π g from rfl, hρ'π, hρ_one h1, MonoidHom.id_apply]
  have hρ'_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ' ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ' x).comp (ρ' y) := by
    intro x y h
    refine QuotientGroup.monoidHom_ext M ?_
    ext g
    simp only [MonoidHom.comp_apply]
    rw [show QuotientGroup.mk' M g = π g from rfl, hρ'π, hρ'π, hρ'π, hρ_mul x y h,
      MonoidHom.comp_apply]
  have hρ'_add : ∀ (x y : ↥Λ) (g' : G ⧸ M), ρ' (x + y) g' = ρ' x g' * ρ' y g' := by
    intro x y g'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M g'
    rw [show QuotientGroup.mk' M g = π g from rfl, hρ'π, hρ'π, hρ'π, hρ_add, map_mul]
  let N' : Subgroup (G ⧸ M) := N.map π
  have hN'fin : (N' : Set (G ⧸ M)).Finite := by
    rw [Subgroup.coe_map]; exact hN.image _
  have hstab' : ∀ (x : ↥Λ) (g' : G ⧸ M), g' ∈ N' → ρ' x g' ∈ N' := by
    intro x g' hg'
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hg'
    rw [hρ'π]
    exact Subgroup.mem_map_of_mem _ (hstab x g hg)
  have hcardNN' : Nat.card M * Nat.card N' = Nat.card N := by
    have h1 : M.relIndex N = Nat.card N' := by
      have := Subgroup.relIndex_ker N π
      rwa [hπker] at this
    have h2 := Subgroup.relIndex_mul_relIndex ⊥ M N bot_le hMN
    rwa [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, h1] at h2
  haveI : Finite N' := Set.finite_coe_iff.mpr hN'fin
  have hN'pos : 0 < Nat.card N' := Nat.card_pos
  have hlt : Nat.card N' < n := by
    rw [← hcard, ← hcardNN', hcardM]
    exact lt_mul_left hN'pos (Nat.one_lt_pow two_ne_zero hℓ₀.one_lt)
  obtain ⟨e', ℓ', H', hℓ', hH'0, hH'last, hH'mono, hH'stab, hH'idx, hH'pow, hH'ram, hH'card⟩ :=
    ih _ hlt ρ' hρ'_one hρ'_mul hρ'_add N' hN'fin hstab' rfl

  have hH1 : (H' 0).comap π = M := by
    rw [hH'0, MonoidHom.comap_bot, hπker]
  refine ⟨e' + 1, Fin.cons ℓ₀ ℓ', Fin.cons ⊥ (fun j => (H' j).comap π), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using hℓ₀
    · simpa using hℓ' i
  · simp
  · rw [← Fin.succ_last, Fin.cons_succ, hH'last]
    exact Subgroup.comap_map_eq_self (by rw [hπker]; exact hMN)
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
      exact Subgroup.comap_mono (hH'mono i)
  · intro j x g hg
    revert hg
    refine Fin.cases ?_ (fun i => ?_) j
    · intro hg
      simp only [Fin.cons_zero, Subgroup.mem_bot] at hg ⊢
      rw [hg, map_one]
    · intro hg
      simp only [Fin.cons_succ, Subgroup.mem_comap] at hg ⊢
      rw [← hρ'π]
      exact hH'stab i x _ hg
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, Subgroup.relIndex_bot_left]
      rw [hH1, hcardM]
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ,
        Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective M)]
      exact hH'idx i
  · intro j g
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, Subgroup.mem_bot]
      rw [hH1]
      exact hpowM g
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Subgroup.mem_comap,
        Subgroup.mem_comap, map_pow]
      exact hH'pow i (π g)
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_succ, Subgroup.mem_bot]
      rw [hH1]
      exact hramM
    · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
      intro hor g hg m k hmk
      rw [Subgroup.mem_comap] at hg ⊢
      rw [← hρ'π]
      exact hH'ram i hor (π g) hg m k hmk
  · rw [Fin.prod_univ_succ, Fin.cons_zero, ← hcardNN', hcardM, hH'card]
    simp only [Fin.cons_succ]

end Main

end P2M.ChainSubgroupRelIndexSq

open P2M.ChainSubgroupRelIndexSq in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {G : Type*} [CommGroup G] (ρ : ↥Λ → G →* G)
    (hρ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h1⟩ = MonoidHom.id G)
    (hρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (hρ_add : ∀ (x y : ↥Λ) (g : G), ρ (x + y) g = ρ x g * ρ y g)
    (N : Subgroup G) (hN : (N : Set G).Finite) (hstab : ∀ (x : ↥Λ) (g : G), g ∈ N → ρ x g ∈ N) :
    ∃ (e : ℕ) (ℓ : Fin e → ℕ) (H : Fin (e + 1) → Subgroup G),
      (∀ j, (ℓ j).Prime) ∧ H 0 = ⊥ ∧ H (Fin.last e) = N ∧
      (∀ j : Fin e, H j.castSucc ≤ H j.succ) ∧
      (∀ (j : Fin (e + 1)) (x : ↥Λ) (g : G), g ∈ H j → ρ x g ∈ H j) ∧
      (∀ j : Fin e, (H j.castSucc).relIndex (H j.succ) = ℓ j ^ 2) ∧
      (∀ (j : Fin e) (g : G), g ∈ H j.succ → g ^ (ℓ j) ∈ H j.castSucc) ∧
      (∀ j : Fin e, (ℓ j = q ∨ ℓ j = q') → ∀ g : G, g ∈ H j.succ →
        ∀ (m : ↥Λ) (k : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((ℓ j : ℤ) * k : ℚ) : ℍ[ℚ, a, b]) →
          ρ m g ∈ H j.castSucc) ∧
      Nat.card N = ∏ j, ℓ j ^ 2 :=
  main hqq' hB Λ hΛ (Nat.card N) ρ hρ_one hρ_mul hρ_add N hN hstab rfl

end S_QuaternionAlgebra_IsMaximalOrder_exists_chain_subgroup_relIndex_eq_sq
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_chain_subgroup_relIndex_eq_sq (solution)
