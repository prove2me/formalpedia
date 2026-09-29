-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/17e7d8c9-35db-51f3-a25d-caf91ef2a055

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top
import Theorems.Thm_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace DCb

variable {a b : ℚ}

theorem sl2Lines {F : Type*} [Field F]
    (I I' : Submodule (Matrix (Fin 2) (Fin 2) F) (Matrix (Fin 2) (Fin 2) F))
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (hI'0 : I' ≠ ⊥) (hI'1 : I' ≠ ⊤) :
    ∃ g : Matrix (Fin 2) (Fin 2) F, g.det = 1 ∧ (g - 1) * (g - 1) = 0 ∧ g ≠ 1 ∧ ∀ A ∈ I, A * g ∈ I' :=
  Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top I I' hI0 hI1 hI'0 hI'1

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

theorem mul_self_eq {x : ℍ[ℚ, a, b]} {n t : ℤ} (hn : (n : ℚ) = nrd x) (ht : (t : ℚ) = trd x) :
    x * x = t • x - n • (1 : ℍ[ℚ, a, b]) := by
  have h1 : x * (x + star x) = x * x + ((nrd x : ℚ) : ℍ[ℚ, a, b]) := by rw [mul_add, mul_star_eq_coe_nrd]
  rw [add_star_eq_coe_trd, ← coe_commutes, coe_mul_eq_smul, ← ht, ← hn, Int.cast_smul_eq_zsmul] at h1
  have h3 : (((n : ℤ) : ℚ) : ℍ[ℚ, a, b]) = n • (1 : ℍ[ℚ, a, b]) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
  rw [h3] at h1
  rw [h1]; abel

theorem cast_eq_one_of_unipotent {p : ℕ} [Fact p.Prime] {g : Matrix (Fin 2) (Fin 2) (ZMod p)} {t n : ℤ}
    (hg2 : (g - 1) * (g - 1) = 0) (hg1 : g ≠ 1) (hch : g * g = (t : ZMod p) • g - (n : ZMod p) • 1) :
    ((n : ℤ) : ZMod p) = 1 := by
  have hsq : g * g = (2 : ZMod p) • g - 1 := by
    have e : (g - 1) * (g - 1) = g * g - (2 : ZMod p) • g + 1 := by
      rw [sub_mul, mul_sub, mul_sub, mul_one, one_mul, one_mul, two_smul]; abel
    rw [e] at hg2
    rw [← sub_eq_zero, ← hg2]; abel
  have e1 : (t : ZMod p) • g - (n : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) = (2 : ZMod p) • g - 1 :=
    hch.symm.trans hsq
  have key : ((t : ZMod p) - 2) • g = ((n : ZMod p) - 1) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [sub_smul, sub_smul, one_smul]
    rw [sub_eq_sub_iff_add_eq_add]
    rw [sub_eq_iff_eq_add] at e1
    rw [e1]; abel
  by_cases ht : (t : ZMod p) - 2 = 0
  · rw [ht, zero_smul] at key
    have h00 := congrFun (congrFun key 0) 0
    simp at h00
    linear_combination (-1 : ZMod p) * h00
  · exfalso
    apply hg1
    set lam : ZMod p := ((t : ZMod p) - 2)⁻¹ * ((n : ZMod p) - 1) with hlam
    have hg : g = lam • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      rw [hlam, mul_smul, ← key, smul_smul, inv_mul_cancel₀ ht, one_smul]
    have h1' : g - 1 = (lam - 1) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by rw [hg, sub_smul, one_smul]
    rw [h1', smul_mul_smul_comm, one_mul] at hg2
    rcases smul_eq_zero.mp hg2 with h | h
    · have : lam = 1 := by rwa [mul_self_eq_zero, sub_eq_zero] at h
      rw [hg, this, one_smul]
    · exact absurd h one_ne_zero

theorem exists_nrd_add_zsmul {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x w : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) (hw : w ∈ Λ) (m : ℤ) :
    ∃ j : ℤ, nrd (x + m • w) = nrd x + (m : ℚ) * (j : ℚ) := by
  obtain ⟨n₁, hn₁⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hx).1
  obtain ⟨n₂, hn₂⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hw).1
  obtain ⟨n₃, hn₃⟩ := (hΛ.exists_intCast_eq_nrd_and_exists_intCast_eq_trd (add_mem hx hw)).1
  refine ⟨n₃ - n₁ - n₂ + m * n₂, ?_⟩
  have key : nrd (x + m • w) = nrd x + (m : ℚ) * (nrd (x + w) - nrd x - nrd w) + (m : ℚ) ^ 2 * nrd w := by
    rw [zsmul_eq_ratCast_smul]
    obtain ⟨x₀, x₁, x₂, x₃⟩ := x
    obtain ⟨w₀, w₁, w₂, w₃⟩ := w
    simp only [nrd, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
      QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul,
      QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, smul_eq_mul]
    ring
  rw [key, ← hn₁, ← hn₂, ← hn₃]; push_cast; ring

end DCb

namespace DCb

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

end DCb

namespace DCb

variable {a b : ℚ}

def mulSub {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛo : IsOrder Λ) {p : ℕ} (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p))
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ) (t : ℍ[ℚ, a, b]) (ht : t ∈ Λ) :
    Submodule (Matrix (Fin 2) (Fin 2) (ZMod p)) (Matrix (Fin 2) (Fin 2) (ZMod p)) where
  carrier := {μ | ∃ m, ∃ hm : m ∈ Λ, μ = φ ⟨m * t, hΛo.mul_mem hm ht⟩}
  zero_mem' := ⟨0, zero_mem _, by
    rw [← map_zero φ]; congr 1; exact Subtype.ext (by simp)⟩
  add_mem' := by
    rintro μ ν ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    refine ⟨m + m', add_mem hm hm', ?_⟩
    rw [← map_add]; congr 1; exact Subtype.ext (by simp [add_mul])
  smul_mem' := by
    rintro X μ ⟨m, hm, rfl⟩
    obtain ⟨x, rfl⟩ := hφsurj X
    refine ⟨x * m, hΛo.mul_mem x.2 hm, ?_⟩
    rw [smul_eq_mul, ← hφmul x ⟨m * t, hΛo.mul_mem hm ht⟩ (by rw [← mul_assoc]; exact hΛo.mul_mem (hΛo.mul_mem x.2 hm) ht)]
    congr 1; exact Subtype.ext (mul_assoc _ _ _).symm

theorem mem_mulSub {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛo : IsOrder Λ) {p : ℕ} (φ : ↥Λ →ₗ[ℤ] Matrix (Fin 2) (Fin 2) (ZMod p))
    (hφmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      φ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = φ x * φ y)
    (hφsurj : Function.Surjective φ) (t : ℍ[ℚ, a, b]) (ht : t ∈ Λ) (μ : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    μ ∈ mulSub hΛo φ hφmul hφsurj t ht ↔ ∃ m, ∃ hm : m ∈ Λ, μ = φ ⟨m * t, hΛo.mul_mem hm ht⟩ := Iff.rfl

theorem star_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛo : IsOrder Λ) {t : ℍ[ℚ, a, b]} (ht : t ∈ Λ) : star t ∈ Λ := by
  obtain ⟨τ, hτ⟩ := (hΛo.exists_intCast_eq_nrd_and_exists_intCast_eq_trd ht).2
  have h : star t = ((trd t : ℚ) : ℍ[ℚ, a, b]) - t := by rw [← add_star_eq_coe_trd]; abel
  rw [h, ← hτ]
  refine sub_mem ?_ ht
  rw [show (((τ : ℤ) : ℚ) : ℍ[ℚ, a, b]) = (τ : ℤ) • (1 : ℍ[ℚ, a, b]) by
    rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]]
  exact Λ.smul_mem _ hΛo.one_mem

theorem nrd_ratCast_smul (q : ℚ) (x : ℍ[ℚ, a, b]) : nrd (q • x) = q ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [nrd, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  ring

theorem natCast_smul_eq_mul_star_mul {t : ℍ[ℚ, a, b]} {ℓ : ℕ} (hnt : nrd t = (ℓ : ℚ)) (z : ℍ[ℚ, a, b]) :
    (ℓ : ℤ) • z = z * star t * t := by
  rw [mul_assoc, star_mul_eq_coe_nrd, hnt, ← coe_commutes, coe_mul_eq_smul, natCast_zsmul_eq_ratCast_smul]

theorem mul_right_cancel_of_nrd_ne_zero {t : ℍ[ℚ, a, b]} (hnt : nrd t ≠ 0) {x y : ℍ[ℚ, a, b]} (h : x * t = y * t) :
    x = y := by
  have h' := congrArg (fun u => (nrd t)⁻¹ • (u * star t)) h
  simp only [mul_assoc, mul_star_eq_coe_nrd, ← coe_commutes, coe_mul_eq_smul, smul_smul, inv_mul_cancel₀ hnt,
    one_smul] at h'
  exact h'

theorem transv {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛo : IsOrder Λ) {N : ℕ} (hN0 : N ≠ 0) (hN : Squarefree N)
    (J' : Submodule ℤ ℍ[ℚ, a, b]) (h1 : Λ ≤ J') (h2 : ∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J')
    (h3 : ∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) (h4 : Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) {t : ℍ[ℚ, a, b]} (ht : t ∈ Λ) (hnt : nrd t = (ℓ : ℚ))
    (hlev : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) :
    ¬ ∀ y ∈ J', ∃ m ∈ Λ, ∃ z ∈ Λ, (N : ℤ) • y = m * t + (ℓ : ℤ) • z := by
  intro hall
  obtain ⟨m₀, hm₀⟩ := hℓN
  have hℓm₀ : ¬ ℓ ∣ m₀ := not_dvd_of_squarefree hN hℓ hm₀
  have hnt0 : nrd t ≠ 0 := by rw [hnt]; exact Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hNz : (N : ℤ) = (ℓ : ℤ) * (m₀ : ℤ) := by rw [hm₀]; push_cast; ring

  have step1 : ∀ y ∈ J', ∃ lam ∈ Λ, (N : ℤ) • y = lam * t := by
    intro y hy
    obtain ⟨m, hm, z, hz, e⟩ := hall y hy
    exact ⟨m + z * star t, add_mem hm (hΛo.mul_mem hz (star_mem hΛo ht)),
      by rw [e, natCast_smul_eq_mul_star_mul hnt z, add_mul]⟩

  have step2 : ∀ j ∈ J', ∃ j₁ ∈ J', ∃ m₁ ∈ Λ, j = j₁ * star t + m₁ := by
    intro j hj
    obtain ⟨j₁, hj₁, m₁, hm₁, e⟩ := (hlev (j * t)).mpr ⟨j, hj, rfl⟩
    refine ⟨j₁, hj₁, m₁, hm₁, mul_right_cancel_of_nrd_ne_zero hnt0 ?_⟩
    rw [add_mul, ← natCast_smul_eq_mul_star_mul hnt j₁, e]

  have step3 : ∀ j ∈ J', (m₀ : ℤ) • j ∈ Λ := by
    intro j hj
    obtain ⟨j₁, hj₁, m₁, hm₁, e⟩ := step2 j hj
    obtain ⟨lam, hlam, e1⟩ := step1 j₁ hj₁
    have h : (m₀ : ℤ) • (j₁ * star t) = lam := by
      apply mul_right_cancel_of_nrd_ne_zero hnt0
      rw [smul_mul_assoc, ← natCast_smul_eq_mul_star_mul hnt j₁, smul_smul, ← e1, mul_comm, hNz]
    rw [e, smul_add, h]
    exact add_mem hlam (Λ.smul_mem _ hm₁)

  have hle : nsub N J' ≤ nsub ℓ Λ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_nsub.mp hx
    exact mem_nsub.mpr ⟨(m₀ : ℤ) • y, step3 y hy, by rw [smul_smul, hNz]⟩
  have hNJΛ : nsub N J' ≤ Λ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_nsub.mp hx
    exact h3 y hy
  have hNΛNJ : nsub N Λ ≤ nsub N J' := nsub_mono h1
  have hidx1 : (nsub N Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = N ^ 4 :=
    relIndex_nsub_self hΛo N (Nat.pos_of_ne_zero hN0)
  have hidx2 : (nsub N Λ).toAddSubgroup.relIndex (nsub N J').toAddSubgroup = N ^ 2 := by
    rw [relIndex_nsub_nsub hN0, h4]
  have hidx3 : (nsub N J').toAddSubgroup.relIndex Λ.toAddSubgroup = N ^ 2 := by
    have h' := AddSubgroup.relIndex_mul_relIndex (nsub N Λ).toAddSubgroup (nsub N J').toAddSubgroup
      Λ.toAddSubgroup (fun x hx => hNΛNJ hx) (fun x hx => hNJΛ hx)
    rw [hidx1, hidx2, show N ^ 4 = N ^ 2 * N ^ 2 by ring] at h'
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hN0) 2) h'
  have hidx4 : (nsub ℓ Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 4 := relIndex_nsub_self hΛo ℓ hℓ.pos
  have hchain := AddSubgroup.relIndex_mul_relIndex (nsub N J').toAddSubgroup (nsub ℓ Λ).toAddSubgroup
    Λ.toAddSubgroup (fun x hx => hle hx)
    (fun x hx => by obtain ⟨y, hy, rfl⟩ := mem_nsub.mp hx; exact Λ.smul_mem _ hy)
  rw [hidx3, hidx4] at hchain
  have hdvd : ℓ ^ 4 ∣ N ^ 2 := ⟨_, by rw [← hchain, mul_comm]⟩
  rw [hm₀, mul_pow, show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring] at hdvd
  have hdvd' : ℓ ^ 2 ∣ m₀ ^ 2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hℓ.pos 2) hdvd
  exact hℓm₀ (hℓ.dvd_of_dvd_pow (dvd_trans (dvd_pow_self ℓ two_ne_zero) hdvd'))

end DCb

open DCb in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q')
    (t t' : ℍ[ℚ, a, b]) (ht : t ∈ Λ) (ht' : t' ∈ Λ) (hnt : nrd t = (ℓ : ℚ)) (hnt' : nrd t' = (ℓ : ℚ))
    (hlev : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x)
    (hlev' : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t' = x) ↔ ∃ j ∈ J', j * t' = x) :
    ∃ c ∈ Λ, (∃ k : ℤ, nrd c = 1 + (ℓ : ℚ) * (k : ℚ)) ∧
      (∀ y ∈ J', ∃ y'' ∈ J', ∃ z ∈ Λ, ((N : ℤ) • y) * c = (N : ℤ) • y'' + (ℓ : ℤ) • z) ∧
      (∀ m ∈ Λ, ∃ m' ∈ Λ, ∃ z ∈ Λ, m * t * c = m' * t' + (ℓ : ℤ) • z) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N
  have hℓ0q : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  obtain ⟨h1', h2', h3', h4', -⟩ := hJ'
  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ ℓ hℓq hℓq'

  set I₀ := lineSub φ hφmul hφsurj J' h2' h3' with hI₀
  set I := mulSub hΛo φ hφmul hφsurj t ht with hI
  set I' := mulSub hΛo φ hφmul hφsurj t' ht' with hI'

  have hker : ∀ (x : ℍ[ℚ, a, b]) (hx : x ∈ Λ), φ ⟨x, hx⟩ = 0 → ∃ z ∈ Λ, x = (ℓ : ℤ) • z := by
    intro x hx h0
    obtain ⟨z, hz⟩ := (hφker _).1 h0
    exact ⟨z, z.2, by rw [natCast_zsmul_eq_ratCast_smul]; exact hz⟩
  have hker2 : ∀ (x y : ℍ[ℚ, a, b]) (hx : x ∈ Λ) (hy : y ∈ Λ), φ ⟨x, hx⟩ = φ ⟨y, hy⟩ →
      ∃ z ∈ Λ, x = y + (ℓ : ℤ) • z := by
    intro x y hx hy hxy
    have h0 : φ (⟨x, hx⟩ - ⟨y, hy⟩) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz, e⟩ := hker (x - y) (sub_mem hx hy) h0
    exact ⟨z, hz, by rw [← e]; abel⟩

  have line_ne_bot : ∀ (s : ℍ[ℚ, a, b]) (hs : s ∈ Λ) (hns : nrd s = (ℓ : ℚ)), mulSub hΛo φ hφmul hφsurj s hs ≠ ⊥ := by
    intro s hs hns hbot
    have hmem : φ ⟨1 * s, hΛo.mul_mem hΛo.one_mem hs⟩ ∈ mulSub hΛo φ hφmul hφsurj s hs :=
      (mem_mulSub hΛo φ hφmul hφsurj s hs _).2 ⟨1, hΛo.one_mem, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    obtain ⟨z, hz, e⟩ := hker _ _ hmem
    rw [one_mul] at e
    obtain ⟨n, hn⟩ := (hΛo.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hz).1
    have : nrd s = (ℓ : ℚ) ^ 2 * nrd z := by rw [e, natCast_zsmul_eq_ratCast_smul, nrd_ratCast_smul]
    rw [hns, ← hn] at this
    have h' : (ℓ : ℤ) = (ℓ : ℤ) ^ 2 * n := by exact_mod_cast this
    have hℓz : (ℓ : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hℓ.ne_zero
    have h1 : (ℓ : ℤ) * n = 1 := by
      have : (ℓ : ℤ) * ((ℓ : ℤ) * n) = (ℓ : ℤ) * 1 := by linear_combination h'.symm
      exact mul_left_cancel₀ hℓz this
    have : (ℓ : ℤ) ∣ 1 := ⟨n, h1.symm⟩
    have : ℓ ∣ 1 := by exact_mod_cast this
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp this)

  have nrd_int : ∀ (x : ℍ[ℚ, a, b]), x ∈ Λ → ∃ n : ℤ, (n : ℚ) = nrd x := fun x hx =>
    (hΛo.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hx).1

  have absorb : ∀ (s m z : ℍ[ℚ, a, b]), nrd s = (ℓ : ℚ) → m * s + (ℓ : ℤ) • z = (m + z * star s) * s := by
    intro s m z hns
    rw [natCast_smul_eq_mul_star_mul hns z, add_mul]
  have line_ne_top : ∀ (s : ℍ[ℚ, a, b]) (hs : s ∈ Λ) (hns : nrd s = (ℓ : ℚ)), mulSub hΛo φ hφmul hφsurj s hs ≠ ⊤ := by
    intro s hs hns htop
    have h1m : (1 : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ∈ mulSub hΛo φ hφmul hφsurj s hs := htop ▸ Submodule.mem_top
    obtain ⟨m, hm, e⟩ := (mem_mulSub hΛo φ hφmul hφsurj s hs _).1 h1m
    have e' : φ ⟨1, hΛo.one_mem⟩ = φ ⟨m * s, hΛo.mul_mem hm hs⟩ := by rw [hφ1]; exact e
    obtain ⟨z, hz, e2⟩ := hker2 _ _ _ _ e'
    rw [absorb s m z hns] at e2
    obtain ⟨n, hn⟩ := nrd_int _ (add_mem hm (hΛo.mul_mem hz (star_mem hΛo hs)))
    have h3 : nrd (1 : ℍ[ℚ, a, b]) = nrd (m + z * star s) * nrd s := by rw [← QuaternionAlgebra.nrd_mul, ← e2]
    rw [nrd_one, ← hn, hns] at h3
    have h4 : (1 : ℤ) = n * ℓ := by exact_mod_cast h3
    have : (ℓ : ℤ) ∣ 1 := ⟨n, by rw [h4, mul_comm]⟩
    have : ℓ ∣ 1 := by exact_mod_cast this
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp this)
  have hI0 : I ≠ ⊥ := line_ne_bot t ht hnt
  have hI'0 : I' ≠ ⊥ := line_ne_bot t' ht' hnt'
  have hI1 : I ≠ ⊤ := line_ne_top t ht hnt
  have hI'1 : I' ≠ ⊤ := line_ne_top t' ht' hnt'

  have hI₀ : ∀ (s : ℍ[ℚ, a, b]) (hs : s ∈ Λ) (hns : nrd s = (ℓ : ℚ))
      (hlevs : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * s = x) ↔ ∃ j ∈ J', j * s = x),
      ¬ I₀ ≤ mulSub hΛo φ hφmul hφsurj s hs := by
    intro s hs hns hlevs hle
    by_cases hℓN : ℓ ∣ N
    · apply transv hΛo hN0 hN J' h1' h2' h3' h4' hℓ hℓN hs hns hlevs
      intro y hy
      have hmem : φ ⟨(N : ℤ) • y, h3' y hy⟩ ∈ I₀ := (mem_lineSub φ hφmul hφsurj J' h2' h3' _).2 ⟨y, hy, rfl⟩
      obtain ⟨m, hm, e⟩ := (mem_mulSub hΛo φ hφmul hφsurj s hs _).1 (hle hmem)
      obtain ⟨z, hz, e2⟩ := hker2 _ _ _ _ e
      exact ⟨m, hm, z, hz, e2⟩
    · have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ J' := h1' hΛo.one_mem
      have hmem : φ ⟨(N : ℤ) • (1 : ℍ[ℚ, a, b]), h3' 1 h1Λ⟩ ∈ I₀ :=
        (mem_lineSub φ hφmul hφsurj J' h2' h3' _).2 ⟨1, h1Λ, rfl⟩
      obtain ⟨m, hm, e⟩ := (mem_mulSub hΛo φ hφmul hφsurj s hs _).1 (hle hmem)
      obtain ⟨z, hz, e2⟩ := hker2 _ _ _ _ e
      rw [absorb s m z hns] at e2
      obtain ⟨n, hn⟩ := nrd_int _ (add_mem hm (hΛo.mul_mem hz (star_mem hΛo hs)))
      have h3 : nrd ((N : ℤ) • (1 : ℍ[ℚ, a, b])) = nrd (m + z * star s) * nrd s := by
        rw [← QuaternionAlgebra.nrd_mul, ← e2]
      rw [natCast_zsmul_eq_ratCast_smul, nrd_ratCast_smul, nrd_one, mul_one, ← hn, hns] at h3
      have h4 : ((N : ℤ)) ^ 2 = n * ℓ := by exact_mod_cast h3
      have : (ℓ : ℤ) ∣ (N : ℤ) ^ 2 := ⟨n, by rw [h4, mul_comm]⟩
      have : ℓ ∣ N ^ 2 := by exact_mod_cast this
      exact hℓN (hℓ.dvd_of_dvd_pow this)

  obtain ⟨g, -, hg2, hI₀g, hmove⟩ :=
    Matrix.exists_det_eq_one_unipotent_forall_mul_mem_of_not_le_of_not_le I₀ I I' hI0 hI1 hI'0 hI'1
      (hI₀ t ht hnt hlev) (hI₀ t' ht' hnt' hlev')

  have key : ∀ (c : ℍ[ℚ, a, b]) (hc : c ∈ Λ), φ ⟨c, hc⟩ = g → (∃ k : ℤ, nrd c = 1 + (ℓ : ℚ) * (k : ℚ)) →
      ∃ c ∈ Λ, (∃ k : ℤ, nrd c = 1 + (ℓ : ℚ) * (k : ℚ)) ∧
        (∀ y ∈ J', ∃ y'' ∈ J', ∃ z ∈ Λ, ((N : ℤ) • y) * c = (N : ℤ) • y'' + (ℓ : ℤ) • z) ∧
        (∀ m ∈ Λ, ∃ m' ∈ Λ, ∃ z ∈ Λ, m * t * c = m' * t' + (ℓ : ℤ) • z) := by
    intro c hc hφc hk
    refine ⟨c, hc, hk, ?_, ?_⟩
    · intro y hy
      have h := hI₀g _ ((mem_lineSub φ hφmul hφsurj J' h2' h3' _).2 ⟨y, hy, rfl⟩)
      obtain ⟨y'', hy'', e⟩ := (mem_lineSub φ hφmul hφsurj J' h2' h3' _).1 h
      have hmem2 : ((N : ℤ) • y) * c ∈ Λ := hΛo.mul_mem (h3' y hy) hc
      have e3 : φ ⟨((N : ℤ) • y) * c, hmem2⟩ = φ ⟨(N : ℤ) • y'', h3' y'' hy''⟩ := by
        rw [hφmul ⟨(N : ℤ) • y, h3' y hy⟩ ⟨c, hc⟩ hmem2, hφc]; exact e
      obtain ⟨z, hz, e4⟩ := hker2 _ _ _ _ e3
      exact ⟨y'', hy'', z, hz, e4⟩
    · intro m hm
      have h := hmove _ ((mem_mulSub hΛo φ hφmul hφsurj t ht _).2 ⟨m, hm, rfl⟩)
      obtain ⟨m', hm', e⟩ := (mem_mulSub hΛo φ hφmul hφsurj t' ht' _).1 h
      have hmem2 : m * t * c ∈ Λ := hΛo.mul_mem (hΛo.mul_mem hm ht) hc
      have e3 : φ ⟨m * t * c, hmem2⟩ = φ ⟨m' * t', hΛo.mul_mem hm' ht'⟩ := by
        rw [hφmul ⟨m * t, hΛo.mul_mem hm ht⟩ ⟨c, hc⟩ hmem2, hφc]; exact e
      obtain ⟨z, hz, e4⟩ := hker2 _ _ _ _ e3
      exact ⟨m', hm', z, hz, e4⟩
  by_cases hg1 : g = 1
  · exact key 1 hΛo.one_mem (by rw [hφ1, hg1]) ⟨0, by simp [nrd_one]⟩
  · obtain ⟨c, hc⟩ := hφsurj g
    refine key c c.2 hc ?_

    obtain ⟨⟨n, hn⟩, ⟨τ, hτ⟩⟩ := hΛo.exists_intCast_eq_nrd_and_exists_intCast_eq_trd c.2
    have hsq := mul_self_eq hn hτ
    have hmem : (c : ℍ[ℚ, a, b]) * c ∈ Λ := hΛo.mul_mem c.2 c.2
    have hch : g * g = (τ : ZMod ℓ) • g - (n : ZMod ℓ) • 1 := by
      have e1 : φ ⟨(c : ℍ[ℚ, a, b]) * c, hmem⟩ = g * g := by rw [hφmul c c hmem, hc]
      have e2 : (⟨(c : ℍ[ℚ, a, b]) * c, hmem⟩ : ↥Λ) = τ • c - n • ⟨1, hΛo.one_mem⟩ :=
        Subtype.ext (by simpa using hsq)
      rw [← e1, e2, map_sub, map_zsmul, map_zsmul, hc, hφ1, ← Int.cast_smul_eq_zsmul (ZMod ℓ) τ,
        ← Int.cast_smul_eq_zsmul (ZMod ℓ) n]
    have hn1 := cast_eq_one_of_unipotent hg2 hg1 hch
    have hdv : ((n - 1 : ℤ) : ZMod ℓ) = 0 := by push_cast; rw [hn1, sub_self]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (n - 1) ℓ).1 hdv
    refine ⟨k, ?_⟩
    rw [← hn]
    have : n = 1 + (ℓ : ℤ) * k := by linarith
    exact_mod_cast this

end S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_one_add_and_forall_smul_mul_eq_and_forall_mul_mul_eq_of_levelIdentity (solution)
