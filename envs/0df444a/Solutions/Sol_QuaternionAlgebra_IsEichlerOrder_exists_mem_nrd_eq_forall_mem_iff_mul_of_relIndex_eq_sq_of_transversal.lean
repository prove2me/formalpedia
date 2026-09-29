-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_mem_nrd_eq_forall_mem_iff_mul_of_relIndex_eq_sq_of_transversal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e4e6ddb7-0535-59f4-859d-7862f0bff513

import Mathlib
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_neg_one
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_nrd_eq_forall_mem_iff_mul_of_relIndex_eq_sq_of_transversal
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace ExistTransversal

variable {a b : ℚ}

theorem zsmul_eq_ratCast_smul (n : ℤ) (x : ℍ[ℚ, a, b]) : n • x = (n : ℚ) • x :=
  (Int.cast_smul_eq_zsmul ℚ n x).symm

theorem natCast_zsmul_eq_ratCast_smul (n : ℕ) (x : ℍ[ℚ, a, b]) : (n : ℤ) • x = (n : ℚ) • x := by
  rw [zsmul_eq_ratCast_smul]; push_cast; rfl

theorem zsmul_right_cancel {n : ℤ} (hn : n ≠ 0) {x y : ℍ[ℚ, a, b]} (h : n • x = n • y) : x = y := by
  rw [zsmul_eq_ratCast_smul, zsmul_eq_ratCast_smul] at h
  exact smul_right_injective ℍ[ℚ, a, b] (Int.cast_ne_zero.mpr hn) h

def nsub (n : ℕ) (X : Submodule ℤ ℍ[ℚ, a, b]) : Submodule ℤ ℍ[ℚ, a, b] :=
  X.map ((n : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b]))

theorem mem_nsub {n : ℕ} {X : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ[ℚ, a, b]} :
    x ∈ nsub n X ↔ ∃ y ∈ X, (n : ℤ) • y = x := by
  simp [nsub, Submodule.mem_map]

theorem relIndex_nsub_nsub {n : ℕ} (hn : n ≠ 0) (X Y : Submodule ℤ ℍ[ℚ, a, b]) :
    (nsub n X).toAddSubgroup.relIndex (nsub n Y).toAddSubgroup = X.toAddSubgroup.relIndex Y.toAddSubgroup := by
  simp only [nsub, Submodule.map_toAddSubgroup]
  refine AddSubgroup.relIndex_map_map_of_injective _ _ ?_
  intro x y hxy
  have : (n : ℤ) • x = (n : ℤ) • y := by simpa using hxy
  exact zsmul_right_cancel (Int.natCast_ne_zero.mpr hn) this

theorem nrd_mul' (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem star_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨t, ht⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hx).2
  have e : star x = ((trd x : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← add_star_eq_coe_trd]; abel
  rw [e, ← ht]
  refine sub_mem ?_ hx
  have : (((t : ℤ) : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [this]; exact Λ.smul_mem t hΛ.one_mem

theorem toAddSubgroup_sup (p p' : Submodule ℤ ℍ[ℚ, a, b]) :
    (p ⊔ p').toAddSubgroup = p.toAddSubgroup ⊔ p'.toAddSubgroup := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    exact AddSubgroup.mem_sup.2 ⟨y, hy, z, hz, rfl⟩
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hx
    exact Submodule.mem_sup.2 ⟨y, hy, z, hz, rfl⟩

end ExistTransversal

open ExistTransversal in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (J : Submodule ℤ ℍ[ℚ, a, b]) (hJΛ : J ≤ Λ) (hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J)
    (hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J)
    (hidx : J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2)
    (htrans : ∀ y ∈ J', (ℓ : ℤ) • y ∈ J → y ∈ Λ) :
    ∃ t ∈ R, nrd t = (ℓ : ℚ) ∧
      (∀ x : ℍ[ℚ, a, b], x ∈ J ↔ ∃ m ∈ Λ, m * t = x) ∧
      (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) := by
  classical
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨h1, h2, h3, h4, h5⟩ := hJ'

  obtain ⟨s₀, hs₀Λ, hs₀nrd, hs₀J⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt
      hqq' hB Λ hΛ ℓ hℓ J hJΛ hℓJ hleft hidx
  obtain ⟨s, hsΛ, hsnrd, hsJ⟩ : ∃ s ∈ Λ, nrd s = (ℓ : ℚ) ∧ ∀ x : ℍ[ℚ, a, b], x ∈ J ↔ ∃ m ∈ Λ, x = m * s := by
    rcases hs₀nrd with hpos | hneg
    · exact ⟨s₀, hs₀Λ, hpos, hs₀J⟩
    · obtain ⟨ε, ⟨hεΛ, ε', hε'Λ, hεε', hε'ε⟩, hεnrd⟩ :=
        QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_neg_one hB Λ hΛ
      refine ⟨ε * s₀, hΛo.mul_mem hεΛ hs₀Λ, by rw [nrd_mul', hεnrd, hneg]; ring, fun x => ?_⟩
      rw [hs₀J]
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m * ε', hΛo.mul_mem hm hε'Λ, by rw [mul_assoc, ← mul_assoc ε', hε'ε, one_mul]⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m * ε, hΛo.mul_mem hm hεΛ, by rw [mul_assoc]⟩
  have hsbΛ : star s ∈ Λ := star_mem hΛo hsΛ
  have hsbs : star s * s = ((ℓ : ℚ) : ℍ[ℚ, a, b]) := by rw [star_mul_eq_coe_nrd, hsnrd]
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hs0 : s ≠ 0 := by
    intro h; apply hℓ0; rw [← hsnrd, h, nrd_zero]

  let fR : ℍ[ℚ, a, b] → ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b] := fun y => LinearMap.mulRight ℤ y
  have hfR : ∀ y x, fR y x = x * y := fun y x => rfl
  have hfs_inj : Function.Injective (fR s) := by
    intro x y hxy
    rw [hfR, hfR] at hxy
    have hu : IsUnit s := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB s hs0
    exact hu.mul_left_injective hxy

  set K : Submodule ℤ ℍ[ℚ, a, b] := Λ ⊔ J'.map (fR (star s)) with hK
  have hK1 : Λ ≤ K := le_sup_left
  have hK2 : ∀ x ∈ Λ, ∀ y ∈ K, x * y ∈ K := by
    intro x hx y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨j, hj, rfl⟩ := Submodule.mem_map.1 hy₂
    rw [mul_add]
    refine Submodule.mem_sup.2 ⟨x * y₁, hΛo.mul_mem hx hy₁, x * fR (star s) j,
      Submodule.mem_map.2 ⟨x * j, h2 x hx j hj, by rw [hfR, hfR, mul_assoc]⟩, rfl⟩
  have hK3 : ∀ y ∈ K, ((N : ℤ) • y) ∈ Λ := by
    intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨j, hj, rfl⟩ := Submodule.mem_map.1 hy₂
    rw [smul_add, hfR, ← smul_mul_assoc]
    exact add_mem (Λ.smul_mem _ hy₁) (hΛo.mul_mem (h3 j hj) hsbΛ)

  have hΛs : Λ.map (fR s) = J := by
    ext x
    rw [Submodule.mem_map, hsJ]
    constructor
    · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, (hfR s m).symm ▸ rfl⟩
    · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, hfR s m⟩
  have hJ's : (J'.map (fR (star s))).map (fR s) = nsub ℓ J' := by
    ext x
    simp only [Submodule.mem_map, mem_nsub]
    constructor
    · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩
      refine ⟨j, hj, ?_⟩
      rw [hfR, hfR, mul_assoc, hsbs, ← coe_commutes, coe_mul_eq_smul, natCast_zsmul_eq_ratCast_smul]
    · rintro ⟨j, hj, rfl⟩
      refine ⟨fR (star s) j, ⟨j, hj, rfl⟩, ?_⟩
      rw [hfR, hfR, mul_assoc, hsbs, ← coe_commutes, coe_mul_eq_smul, natCast_zsmul_eq_ratCast_smul]
  have hKs : K.map (fR s) = J ⊔ nsub ℓ J' := by rw [hK, Submodule.map_sup, hΛs, hJ's]

  have htr : (J ⊓ nsub ℓ J' : Submodule ℤ ℍ[ℚ, a, b]) = nsub ℓ Λ := by
    apply le_antisymm
    · rintro x ⟨hxJ, hx'⟩
      obtain ⟨y, hy, rfl⟩ := mem_nsub.1 hx'
      exact mem_nsub.2 ⟨y, htrans y hy hxJ, rfl⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_nsub.1 hx
      exact ⟨hℓJ y hy, mem_nsub.2 ⟨y, h1 hy, rfl⟩⟩
  have hK4 : Λ.toAddSubgroup.relIndex K.toAddSubgroup = N ^ 2 := by
    have e1 := AddSubgroup.relIndex_map_map_of_injective (f := (fR s).toAddMonoidHom) Λ.toAddSubgroup K.toAddSubgroup hfs_inj
    have e2 : (Λ.map (fR s)).toAddSubgroup.relIndex (K.map (fR s)).toAddSubgroup =
        Λ.toAddSubgroup.relIndex K.toAddSubgroup := e1
    rw [← e2, hΛs, hKs, toAddSubgroup_sup, AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right]
    have e3 : J.toAddSubgroup ⊓ (nsub ℓ J').toAddSubgroup = (nsub ℓ Λ).toAddSubgroup := by
      rw [← htr]; ext x; simp [AddSubgroup.mem_inf, Submodule.mem_inf]
    rw [e3, relIndex_nsub_nsub hℓ.ne_zero, h4]

  obtain ⟨u, ⟨huΛ, v, hvΛ, huv, hvu⟩, hunrd, hKu⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule
      hqN hq'N hqq' hB Λ hΛ hN J' K ⟨h1, h2, h3, h4⟩ ⟨hK1, hK2, hK3, hK4⟩

  set t := u * s with ht
  have htΛ : t ∈ Λ := hΛo.mul_mem huΛ hsΛ

  have hlev1 : ∀ j ∈ J', ∃ j₂ ∈ J', ∃ m ∈ Λ, j * t = (ℓ : ℤ) • j₂ + m * t := by
    intro j hj
    have hju : j * u ∈ K := (hKu (j * u)).2 ⟨j, hj, rfl⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, e⟩ := Submodule.mem_sup.1 hju
    obtain ⟨j₂, hj₂, rfl⟩ := Submodule.mem_map.1 hy₂
    refine ⟨j₂, hj₂, y₁ * v, hΛo.mul_mem hy₁ hvΛ, ?_⟩
    rw [ht, ← mul_assoc, ← e, add_mul, hfR, mul_assoc j₂, hsbs, ← coe_commutes, coe_mul_eq_smul,
      natCast_zsmul_eq_ratCast_smul, add_comm, mul_assoc, ← mul_assoc v, hvu, one_mul]
  have hlev2 : ∀ j ∈ J', ∃ j₃ ∈ J', (ℓ : ℤ) • j = j₃ * t := by
    intro j hj
    have hjs : j * star s ∈ K := Submodule.mem_sup.2 ⟨0, zero_mem _, fR (star s) j, ⟨j, hj, rfl⟩, by rw [zero_add]; rfl⟩
    obtain ⟨j₃, hj₃, e⟩ := (hKu _).1 hjs
    refine ⟨j₃, hj₃, ?_⟩
    rw [ht, ← mul_assoc, ← e, mul_assoc, hsbs, ← coe_commutes, coe_mul_eq_smul, natCast_zsmul_eq_ratCast_smul]
  refine ⟨t, ?_, by rw [ht, nrd_mul', hunrd, hsnrd, one_mul], fun x => ?_, fun x => ?_⟩
  ·
    refine (h5 t htΛ).2 fun y hy => ?_
    obtain ⟨j₂, hj₂, m, hm, e⟩ := hlev1 y hy
    rw [e]
    exact add_mem (J'.smul_mem _ hj₂) (h1 (hΛo.mul_mem hm htΛ))
  ·
    rw [hsJ]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m * v, hΛo.mul_mem hm hvΛ, by rw [ht, mul_assoc, ← mul_assoc v, hvu, one_mul]⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m * u, hΛo.mul_mem hm huΛ, by rw [ht, mul_assoc]⟩
  ·
    constructor
    · rintro ⟨j, hj, m, hm, rfl⟩
      obtain ⟨j₃, hj₃, e⟩ := hlev2 j hj
      exact ⟨j₃ + m, add_mem hj₃ (h1 hm), by rw [add_mul, e]⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨j₂, hj₂, m, hm, e⟩ := hlev1 j hj
      exact ⟨j₂, hj₂, m, hm, e.symm⟩

end S_QuaternionAlgebra_IsEichlerOrder_exists_mem_nrd_eq_forall_mem_iff_mul_of_relIndex_eq_sq_of_transversal
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_mem_nrd_eq_forall_mem_iff_mul_of_relIndex_eq_sq_of_transversal (solution)
