-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/859a32ef-b050-5246-919f-c63170d9d2fd

import Mathlib
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_Matrix_natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace DoubleCoset
p2m_open "DoubleCoset"

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

theorem nsub_mono {n : ℕ} {X Y : Submodule ℤ ℍ[ℚ, a, b]} (h : X ≤ Y) : nsub n X ≤ nsub n Y :=
  Submodule.map_mono h

theorem span_image_eq_nsub (n : ℕ) (X : Submodule ℤ ℍ[ℚ, a, b]) :
    Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (n : ℤ) • y) '' (X : Set ℍ[ℚ, a, b])) = nsub n X := by
  have : (fun y : ℍ[ℚ, a, b] => (n : ℤ) • y) = ⇑((n : ℤ) • (LinearMap.id : ℍ[ℚ, a, b] →ₗ[ℤ] ℍ[ℚ, a, b])) := by
    funext y; simp
  rw [this, ← Submodule.map_span, Submodule.span_eq]; rfl

theorem relIndex_nsub_self {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (n : ℕ) (hn : 0 < n) :
    (nsub n X).toAddSubgroup.relIndex X.toAddSubgroup = n ^ 4 := by
  rw [← span_image_eq_nsub]; exact hX.relIndex_span_smul_eq_pow_four n hn

theorem relIndex_nsub_nsub {n : ℕ} (hn : n ≠ 0) (X Y : Submodule ℤ ℍ[ℚ, a, b]) :
    (nsub n X).toAddSubgroup.relIndex (nsub n Y).toAddSubgroup = X.toAddSubgroup.relIndex Y.toAddSubgroup := by
  simp only [nsub, Submodule.map_toAddSubgroup]
  refine AddSubgroup.relIndex_map_map_of_injective _ _ ?_
  intro x y hxy
  have : (n : ℤ) • x = (n : ℤ) • y := by simpa using hxy
  exact zsmul_right_cancel (Int.natCast_ne_zero.mpr hn) this

theorem not_dvd_of_squarefree {N p m : ℕ} (hN : Squarefree N) (hp : p.Prime) (h : N = p * m) : ¬ p ∣ m := by
  rintro ⟨k, rfl⟩
  have : p * p ∣ N := ⟨k, by rw [h]; ring⟩
  exact hp.not_isUnit (hN p this)

end DoubleCoset

namespace DoubleCoset
p2m_open "DoubleCoset"

variable {a b : ℚ}

def lineSub {Λ : Submodule ℤ ℍ[ℚ, a, b]} {p : ℕ} (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p))
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ) {N : ℕ}
    (J : Submodule ℤ ℍ[ℚ, a, b]) (h2 : ∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J) (h3 : ∀ y ∈ J, ((N : ℤ) • y) ∈ Λ) :
    Submodule (Matrix (Fin 2) (Fin 2) (ZMod p)) (Matrix (Fin 2) (Fin 2) (ZMod p)) where
  carrier := {μ | ∃ y, ∃ hy : y ∈ J, μ = φ ⟨(N : ℤ) • y, h3 y hy⟩}
  zero_mem' := ⟨0, zero_mem _, by
    rw [← map_zero φ]; congr 1; exact Subtype.ext (by simp)⟩
  add_mem' := by
    rintro μ ν ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [← map_add]; congr 1; exact Subtype.ext (by simp [smul_add])
  smul_mem' := by
    rintro X μ ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := hφsurj X
    have hxy : (x : ℍ[ℚ, a, b]) * y ∈ J := h2 x x.2 y hy
    refine ⟨x * y, hxy, ?_⟩
    have hmem : (x : ℍ[ℚ, a, b]) * ((N : ℤ) • y) ∈ Λ := by rw [mul_smul_comm]; exact h3 _ hxy
    rw [smul_eq_mul, ← hφmul x ⟨(N : ℤ) • y, h3 y hy⟩ hmem]
    congr 1; exact Subtype.ext (mul_smul_comm _ _ _)

theorem mem_lineSub {Λ : Submodule ℤ ℍ[ℚ, a, b]} {p : ℕ} (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p))
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ) {N : ℕ}
    (J : Submodule ℤ ℍ[ℚ, a, b]) (h2 : ∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J) (h3 : ∀ y ∈ J, ((N : ℤ) • y) ∈ Λ)
    (μ : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    μ ∈ lineSub φ hφmul hφsurj J h2 h3 ↔ ∃ y, ∃ hy : y ∈ J, μ = φ ⟨(N : ℤ) • y, h3 y hy⟩ := Iff.rfl

theorem image_ne_zero_and_ne_one {N : ℕ} (hN0 : N ≠ 0) (hN : Squarefree N)
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛo : IsOrder Λ)
    (J : Submodule ℤ ℍ[ℚ, a, b]) (h1 : Λ ≤ J) (h2 : ∀ x ∈ Λ, ∀ y ∈ J, x * y ∈ J)
    (h3 : ∀ y ∈ J, ((N : ℤ) • y) ∈ Λ) (h4 : Λ.toAddSubgroup.relIndex J.toAddSubgroup = N ^ 2)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p))
    (hφ1 : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, φ ⟨1, h⟩ = 1)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (p : ℚ) • (y : ℍ[ℚ, a, b])) :
    (∃ y, ∃ hy : y ∈ J, φ ⟨(N : ℤ) • y, h3 y hy⟩ ≠ 0) ∧ (∀ y (hy : y ∈ J), φ ⟨(N : ℤ) • y, h3 y hy⟩ ≠ 1) := by
  have hpN' := hpN
  obtain ⟨m, hm⟩ := hpN'
  have hpm : ¬ p ∣ m := not_dvd_of_squarefree hN hp hm

  have hNJΛ : nsub N J ≤ Λ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_nsub.mp hx
    exact h3 y hy
  have hNΛNJ : nsub N Λ ≤ nsub N J := nsub_mono h1
  have hidx1 : (nsub N Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = N ^ 4 :=
    relIndex_nsub_self hΛo N (Nat.pos_of_ne_zero hN0)
  have hidx2 : (nsub N Λ).toAddSubgroup.relIndex (nsub N J).toAddSubgroup = N ^ 2 := by
    rw [relIndex_nsub_nsub hN0, h4]
  have hidx3 : (nsub N J).toAddSubgroup.relIndex Λ.toAddSubgroup = N ^ 2 := by
    have h' := AddSubgroup.relIndex_mul_relIndex (nsub N Λ).toAddSubgroup (nsub N J).toAddSubgroup
      Λ.toAddSubgroup (fun x hx => hNΛNJ hx) (fun x hx => hNJΛ hx)
    rw [hidx1, hidx2, show N ^ 4 = N ^ 2 * N ^ 2 by ring] at h'
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hN0) 2) h'
  constructor
  · by_contra hall
    push Not at hall

    have hle : nsub N J ≤ nsub p Λ := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_nsub.mp hx
      have h0 : φ ⟨(N : ℤ) • y, h3 y hy⟩ = 0 := hall y hy
      obtain ⟨z, hz⟩ := (hφker _).1 h0
      have hz' : (N : ℤ) • y = (p : ℚ) • (z : ℍ[ℚ, a, b]) := hz
      exact mem_nsub.mpr ⟨z, z.2, by rw [natCast_zsmul_eq_ratCast_smul]; exact hz'.symm⟩
    have hidx4 : (nsub p Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = p ^ 4 := relIndex_nsub_self hΛo p hp.pos
    have hchain := AddSubgroup.relIndex_mul_relIndex (nsub N J).toAddSubgroup (nsub p Λ).toAddSubgroup
      Λ.toAddSubgroup (fun x hx => hle hx)
      (fun x hx => by obtain ⟨y, hy, rfl⟩ := mem_nsub.mp hx; exact Λ.smul_mem _ hy)
    rw [hidx3, hidx4] at hchain
    have hdvd : p ^ 4 ∣ N ^ 2 := ⟨_, by rw [← hchain, mul_comm]⟩
    rw [hm, mul_pow, show p ^ 4 = p ^ 2 * p ^ 2 by ring] at hdvd
    have hdvd' : p ^ 2 ∣ m ^ 2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 2) hdvd
    exact hpm (hp.dvd_of_dvd_pow (dvd_trans (dvd_pow_self p two_ne_zero) hdvd'))
  · intro y hy hy1

    have hker : φ (⟨(N : ℤ) • y, h3 y hy⟩ - ⟨1, hΛo.one_mem⟩) = 0 := by
      rw [map_sub, hy1, hφ1 hΛo.one_mem, sub_self]
    obtain ⟨z, hz⟩ := (hφker _).1 hker
    have hz' : (N : ℤ) • y - 1 = (p : ℚ) • (z : ℍ[ℚ, a, b]) := hz
    have hz'' : (N : ℚ) • y - 1 = (p : ℚ) • (z : ℍ[ℚ, a, b]) := by
      rw [← natCast_zsmul_eq_ratCast_smul]; exact hz'
    have hone : (1 : ℍ[ℚ, a, b]) = (N : ℚ) • y - (p : ℚ) • (z : ℍ[ℚ, a, b]) := by
      rw [← hz'', sub_sub_cancel]
    have hNq : (N : ℚ) = (p : ℚ) * (m : ℚ) := by exact_mod_cast hm
    have hle : nsub m Λ ≤ nsub N J := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := mem_nsub.mp hx
      have hwy : w * y ∈ J := h2 w hw y hy
      have hwz : w * (z : ℍ[ℚ, a, b]) ∈ Λ := hΛo.mul_mem hw z.2
      refine mem_nsub.mpr ⟨(m : ℤ) • (w * y) - w * z, sub_mem (J.smul_mem _ hwy) (h1 hwz), ?_⟩
      have hw1 : w = (N : ℚ) • (w * y) - (p : ℚ) • (w * (z : ℍ[ℚ, a, b])) := by
        conv_lhs => rw [← mul_one w, hone]
        rw [mul_sub, mul_smul_comm, mul_smul_comm]
      simp only [natCast_zsmul_eq_ratCast_smul]
      rw [hNq] at hw1 ⊢
      conv_rhs => rw [hw1]
      module
    have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => hN0 (by rw [hm, h, mul_zero]))
    have hidx5 : (nsub m Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = m ^ 4 := relIndex_nsub_self hΛo m hm0
    have hchain := AddSubgroup.relIndex_mul_relIndex (nsub m Λ).toAddSubgroup (nsub N J).toAddSubgroup
      Λ.toAddSubgroup (fun x hx => hle hx) (fun x hx => hNJΛ hx)
    rw [hidx3, hidx5] at hchain
    have hdvd : p ∣ m ^ 4 := by
      rw [← hchain, hm]; exact Dvd.dvd.mul_left (dvd_pow (dvd_mul_right p m) two_ne_zero) _
    exact hpm (hp.dvd_of_dvd_pow hdvd)

end DoubleCoset

namespace DoubleCoset
p2m_open "DoubleCoset"

variable {a b : ℚ}

def colMap (ℓ : ℕ) (k : Fin 2) : Matrix (Fin 2) (Fin 2) (ZMod ℓ) →ₗ[ℤ] (Fin 2 → ZMod ℓ) where
  toFun A := fun i => A i k
  map_add' A B := by ext i; rfl
  map_smul' n A := by ext i; simp [Matrix.smul_apply]

theorem colMap_apply {ℓ : ℕ} (k : Fin 2) (A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (i : Fin 2) :
    colMap ℓ k A i = A i k := rfl

def annCol (ℓ : ℕ) (k : Fin 2) : Submodule (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) where
  carrier := {A | ∀ i, A i k = 0}
  zero_mem' := fun i => rfl
  add_mem' := fun {A B} hA hB i => by rw [Matrix.add_apply, hA i, hB i, add_zero]
  smul_mem' := fun X A hA i => by
    rw [smul_eq_mul, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [hA j, mul_zero]

theorem mem_annCol {ℓ : ℕ} {k : Fin 2} {A : Matrix (Fin 2) (Fin 2) (ZMod ℓ)} : A ∈ annCol ℓ k ↔ ∀ i, A i k = 0 :=
  Iff.rfl

theorem annCol_ne_bot (ℓ : ℕ) [Fact ℓ.Prime] (k : Fin 2) : annCol ℓ k ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨Matrix.of fun i j => if j = k then 0 else 1, fun i => by simp, fun h => ?_⟩
  have := congrFun (congrFun h 0) (k + 1)
  have hk : k + 1 ≠ k := by fin_cases k <;> decide
  simp [hk] at this

theorem annCol_ne_top (ℓ : ℕ) [Fact ℓ.Prime] (k : Fin 2) : annCol ℓ k ≠ ⊤ := by
  intro h
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ∈ annCol ℓ k := h ▸ Submodule.mem_top
  have := h1 k
  simp at this

theorem exists_colIdeal {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛo : IsOrder Λ) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod ℓ))
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ)
    (hφker : ∀ x : ↥Λ, φ x = 0 ↔ ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (ℓ : ℚ) • (y : ℍ[ℚ, a, b]))
    (k : Fin 2) :
    ∃ J : Submodule ℤ ℍ[ℚ, a, b], J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
      J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧
      (∀ (x : ℍ[ℚ, a, b]) (hx : x ∈ Λ), x ∈ J ↔ ∀ i, φ ⟨x, hx⟩ i k = 0) := by
  classical
  let ψ : ↥Λ →ₗ[ℤ] (Fin 2 → ZMod ℓ) := (colMap ℓ k).comp φ
  have hψ : ∀ x : ↥Λ, ψ x = fun i => φ x i k := fun x => rfl
  let J : Submodule ℤ ℍ[ℚ, a, b] := (LinearMap.ker ψ).map Λ.subtype
  have hJmem : ∀ (x : ℍ[ℚ, a, b]) (hx : x ∈ Λ), x ∈ J ↔ ∀ i, φ ⟨x, hx⟩ i k = 0 := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      have hy' : ψ y = 0 := hy
      have := congrFun hy' i
      exact this
    · intro h
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      show ψ ⟨x, hx⟩ = 0
      ext i; exact h i
  have hJΛ : J ≤ Λ := by
    rintro x ⟨y, -, rfl⟩; exact y.2
  refine ⟨J, hJΛ, ?_, ?_, ?_, hJmem⟩
  ·
    intro y hy
    rw [hJmem _ (Λ.smul_mem _ hy)]
    have h0 : φ ⟨(ℓ : ℤ) • y, Λ.smul_mem _ hy⟩ = 0 :=
      (hφker _).2 ⟨⟨y, hy⟩, natCast_zsmul_eq_ratCast_smul ℓ y⟩
    intro i; rw [h0]; rfl
  ·
    intro m hm x hx
    have hxΛ := hJΛ hx
    rw [hJmem _ (hΛo.mul_mem hm hxΛ)]
    intro i
    rw [hφmul ⟨m, hm⟩ ⟨x, hxΛ⟩ (hΛo.mul_mem hm hxΛ), Matrix.mul_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [(hJmem x hxΛ).1 hx j, mul_zero]
  ·
    have hsurjψ : Function.Surjective ψ := by
      intro v
      obtain ⟨x, hx⟩ := hφsurj (Matrix.of fun i j => if j = k then v i else 0)
      exact ⟨x, by rw [hψ, hx]; ext i; simp⟩
    have hof : J.toAddSubgroup.addSubgroupOf Λ.toAddSubgroup = ψ.toAddMonoidHom.ker := by
      ext ⟨x, hx⟩
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
      show x ∈ J ↔ ψ ⟨x, hx⟩ = 0
      rw [hJmem x hx, hψ]
      exact ⟨fun h => funext h, fun h i => congrFun h i⟩
    rw [AddSubgroup.relIndex, hof, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective _ hsurjψ,
      AddSubgroup.card_top, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_transversal_line
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hN : Squarefree N)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (h1 : Λ ≤ J') (h2 : ∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') (h3 : ∀ y ∈ J', ((N : ℤ) • y) ∈ Λ)
    (h4 : Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    ∃ J : Submodule ℤ ℍ[ℚ, a, b], J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
      J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧ (∀ y ∈ J', (ℓ : ℤ) • y ∈ J → y ∈ Λ) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'

  have bezout : ∀ (m : ℕ), ¬ ℓ ∣ m → ∀ y : ℍ[ℚ, a, b], (ℓ : ℤ) • y ∈ Λ → (m : ℤ) • y ∈ Λ → y ∈ Λ := by
    intro m hm y hℓy hmy
    have hcop : IsCoprime (ℓ : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 (hℓ.coprime_iff_not_dvd.2 hm)
    obtain ⟨α, β, hαβ⟩ := hcop
    have : y = α • ((ℓ : ℤ) • y) + β • ((m : ℤ) • y) := by
      rw [smul_smul, smul_smul, ← add_smul, hαβ, one_smul]
    rw [this]
    exact add_mem (Λ.smul_mem _ hℓy) (Λ.smul_mem _ hmy)
  by_cases hℓN : ℓ ∣ N
  ·
    obtain ⟨m₀, hm⟩ := hℓN
    have hℓm : ¬ ℓ ∣ m₀ := not_dvd_of_squarefree hN hℓ hm
    obtain ⟨⟨y₀, hy₀, hne⟩, hone⟩ := image_ne_zero_and_ne_one hN0 hN hΛo J' h1 h2 h3 h4 hℓ ⟨m₀, hm⟩ φ hφ1 hφker

    obtain ⟨i₀, k, hik⟩ : ∃ i₀ k, φ ⟨(N : ℤ) • y₀, h3 y₀ hy₀⟩ i₀ k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (Matrix.ext fun i j => h i j)
    obtain ⟨J, hJΛ, hℓJ, hleft, hidx, hJmem⟩ := exists_colIdeal (q := q) (q' := q') Λ hΛo ℓ φ hφmul hφsurj hφker k
    refine ⟨J, hJΛ, hℓJ, hleft, hidx, fun y hy hℓy => ?_⟩

    set I₀ := lineSub φ hφmul hφsurj J' h2 h3 with hI₀
    have hI₀0 : I₀ ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨_, (mem_lineSub φ hφmul hφsurj J' h2 h3 _).2 ⟨y₀, hy₀, rfl⟩, hne⟩
    have hI₀1 : I₀ ≠ ⊤ := by
      intro h
      have h1m : (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ∈ I₀ := h ▸ Submodule.mem_top
      obtain ⟨y, hy, e⟩ := (mem_lineSub φ hφmul hφsurj J' h2 h3 _).1 h1m
      exact hone y hy e.symm
    have hIA : I₀ ≠ annCol ℓ k := by
      intro h
      have : φ ⟨(N : ℤ) • y₀, h3 y₀ hy₀⟩ ∈ annCol ℓ k :=
        h ▸ (mem_lineSub φ hφmul hφsurj J' h2 h3 _).2 ⟨y₀, hy₀, rfl⟩
      exact hik (this i₀)
    have hinf : I₀ ⊓ annCol ℓ k = ⊥ :=
      (Matrix.natCard_leftIdeal_ne_bot_ne_top_eq_and_inf_eq_bot ℓ).2 I₀ (annCol ℓ k) hI₀0 hI₀1
        (annCol_ne_bot ℓ k) (annCol_ne_top ℓ k) hIA

    have hℓyΛ : (ℓ : ℤ) • y ∈ Λ := hJΛ hℓy
    have hNy : φ ⟨(N : ℤ) • y, h3 y hy⟩ = 0 := by
      have hmem : φ ⟨(N : ℤ) • y, h3 y hy⟩ ∈ I₀ ⊓ annCol ℓ k := by
        refine ⟨(mem_lineSub φ hφmul hφsurj J' h2 h3 _).2 ⟨y, hy, rfl⟩, fun i => ?_⟩
        have e : (⟨(N : ℤ) • y, h3 y hy⟩ : ↥Λ) = (m₀ : ℤ) • ⟨(ℓ : ℤ) • y, hℓyΛ⟩ :=
          Subtype.ext (by simp only [Submodule.coe_smul, smul_smul]; rw [hm]; push_cast; ring_nf)
        rw [e, map_zsmul, Matrix.smul_apply, (hJmem _ hℓyΛ).1 hℓy i, smul_zero]
      rw [hinf] at hmem
      exact hmem
    obtain ⟨z, hz⟩ := (hφker _).1 hNy
    have hz' : (N : ℤ) • y = (ℓ : ℚ) • (z : ℍ[ℚ, a, b]) := hz
    have hm₀y : (m₀ : ℤ) • y ∈ Λ := by
      have e : (ℓ : ℚ) • ((m₀ : ℤ) • y) = (ℓ : ℚ) • (z : ℍ[ℚ, a, b]) := by
        rw [← hz', ← natCast_zsmul_eq_ratCast_smul, smul_smul, ← Nat.cast_mul, hm]
      have := smul_right_injective ℍ[ℚ, a, b] (show (ℓ : ℚ) ≠ 0 by exact_mod_cast hℓ.ne_zero) e
      rw [this]; exact z.2
    exact bezout m₀ hℓm y hℓyΛ hm₀y
  ·
    obtain ⟨J, hJΛ, hℓJ, hleft, hidx, -⟩ := exists_colIdeal (q := q) (q' := q') Λ hΛo ℓ φ hφmul hφsurj hφker 0
    exact ⟨J, hJΛ, hℓJ, hleft, hidx, fun y hy hℓy => bezout N hℓN y (hJΛ hℓy) (h3 y hy)⟩

end DoubleCoset

open _root_.DoubleCoset _root_.P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule.DoubleCoset in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hN : Squarefree N)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    ∃ J : Submodule ℤ ℍ[ℚ, a, b], J ≤ Λ ∧ (∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J) ∧ (∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J) ∧
      J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 ∧ (∀ y ∈ J', (ℓ : ℤ) • y ∈ J → y ∈ Λ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hJ'
  exact exists_transversal_line hqN hq'N hqq' hB Λ hΛ hN J' h1 h2 h3 h4 ℓ hℓ hℓq hℓq'

end S_QuaternionAlgebra_IsMaximalOrder_exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_submodule_relIndex_eq_sq_and_transversal_of_levelModule (solution)
