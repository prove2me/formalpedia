-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/69c24b29-2a09-597e-8194-90720ab51dd2

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mul_mem_of_levelModule
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace LevmodTransitive

variable {a b : ℚ}

theorem levmodFinite
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hN : Squarefree N)
    (J' J'' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    (hJ'' : Λ ≤ J'' ∧ (∀ x ∈ Λ, ∀ y ∈ J'', x * y ∈ J'') ∧ (∀ y ∈ J'', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J''.toAddSubgroup = N ^ 2) :
    ∃ c ∈ Λ, (∃ k : ℤ, nrd c = 1 + (N : ℚ) * (k : ℚ)) ∧ ∀ y ∈ J', y * c ∈ J'' :=
  QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_forall_mul_mem_of_levelModule hqN hq'N hqq' hB Λ hΛ hN J' J'' hJ' hJ''

theorem saModN
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (c : ℍ[ℚ, a, b]) (hc : c ∈ Λ) (k : ℤ) (hnrd : nrd c = 1 + (N : ℚ) * (k : ℚ)) :
    ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ ∃ z ∈ Λ, u - c = (N : ℤ) • z :=
  QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_one_sub_mem_of_nrd_eq hqN hq'N hqq' hB Λ hΛ c hc k hnrd

end LevmodTransitive

open LevmodTransitive in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hN : Squarefree N)
    (J' J'' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    (hJ'' : Λ ≤ J'' ∧ (∀ x ∈ Λ, ∀ y ∈ J'', x * y ∈ J'') ∧ (∀ y ∈ J'', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J''.toAddSubgroup = N ^ 2) :
    ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ ∀ y : ℍ[ℚ, a, b], y ∈ J'' ↔ ∃ y' ∈ J', y = y' * u := by
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨c, hcΛ, ⟨k, hk⟩, hmove⟩ := levmodFinite hqN hq'N hqq' hB Λ hΛ hN J' J'' hJ' hJ''
  obtain ⟨u, hu, hnrd, z, hz, huz⟩ := saModN hqN hq'N hqq' hB Λ hΛ c hcΛ k hk
  obtain ⟨huΛ, v, hvΛ, huv, hvu⟩ := hu
  refine ⟨u, ⟨huΛ, v, hvΛ, huv, hvu⟩, hnrd, ?_⟩

  have hsub : ∀ y ∈ J', y * u ∈ J'' := by
    intro y hy
    have : y * u = y * c + ((N : ℤ) • y) * z := by
      rw [smul_mul_assoc, ← mul_smul_comm, ← huz, mul_sub]; abel
    rw [this]
    exact add_mem (hmove y hy) (hJ''.1 (hΛo.mul_mem (hJ'.2.2.1 y hy) hz))

  let f : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b] := LinearMap.mulRight ℤ u
  have hf : ∀ x, f x = x * u := fun x => rfl
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h' : x * u * v = y * u * v := by rw [← hf, ← hf, hxy]
    simpa [mul_assoc, huv] using h'
  have hΛf : Λ.map f = Λ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hΛo.mul_mem hx huΛ
    · intro x hx; exact ⟨x * v, hΛo.mul_mem hx hvΛ, by rw [hf, mul_assoc, hvu, mul_one]⟩
  have hKle : J'.map f ≤ J'' := by rintro _ ⟨y, hy, rfl⟩; exact hsub y hy
  have hΛK : Λ ≤ J'.map f := by rw [← hΛf]; exact Submodule.map_mono hJ'.1
  have hidxK : Λ.toAddSubgroup.relIndex (J'.map f).toAddSubgroup = N ^ 2 := by
    have h' := AddSubgroup.relIndex_map_map_of_injective (f := f.toAddMonoidHom) Λ.toAddSubgroup J'.toAddSubgroup hfinj
    have h'' : (Λ.map f).toAddSubgroup.relIndex (J'.map f).toAddSubgroup = Λ.toAddSubgroup.relIndex J'.toAddSubgroup := h'
    rw [hΛf, hJ'.2.2.2] at h''
    exact h''
  have hone : (J'.map f).toAddSubgroup.relIndex J''.toAddSubgroup = 1 := by
    have h' := AddSubgroup.relIndex_mul_relIndex Λ.toAddSubgroup (J'.map f).toAddSubgroup J''.toAddSubgroup
      (fun x hx => hΛK hx) (fun x hx => hKle hx)
    rw [hidxK, hJ''.2.2.2] at h'
    have hN2 : 0 < N ^ 2 := pow_pos (Nat.pos_of_ne_zero hN0) 2
    have : N ^ 2 * (J'.map f).toAddSubgroup.relIndex J''.toAddSubgroup = N ^ 2 * 1 := by rw [mul_one]; exact h'
    exact Nat.eq_of_mul_eq_mul_left hN2 this
  have hKge : J'' ≤ J'.map f := fun x hx => (AddSubgroup.relIndex_eq_one.mp hone) hx
  intro y
  constructor
  · intro hy
    obtain ⟨y', hy', rfl⟩ := hKge hy
    exact ⟨y', hy', (hf y').symm ▸ rfl⟩
  · rintro ⟨y', hy', rfl⟩; exact hsub y' hy'

end S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_isUnitOf_nrd_eq_one_forall_mem_iff_exists_mul_of_levelModule (solution)
