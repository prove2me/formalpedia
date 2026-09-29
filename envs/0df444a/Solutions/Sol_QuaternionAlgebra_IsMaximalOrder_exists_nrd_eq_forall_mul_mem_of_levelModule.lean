-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_forall_mul_mem_of_levelModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1c90d13b-0597-5949-a18b-d1c657f72c4e

import Mathlib
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_Matrix_exists_det_eq_one_unipotent_forall_mul_mem_of_ne_bot_of_ne_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mul_mem_of_levelModule
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

namespace LevmodFinite

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

end LevmodFinite

namespace LevmodFinite

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

theorem local_step {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hN : Squarefree N)
    (J' J'' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    (hJ'' : Λ ≤ J'' ∧ (∀ x ∈ Λ, ∀ y ∈ J'', x * y ∈ J'') ∧ (∀ y ∈ J'', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J''.toAddSubgroup = N ^ 2)
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) (hpq : p ≠ q) (hpq' : p ≠ q') :
    ∃ c ∈ Λ, (∃ k : ℤ, nrd c = 1 + (p : ℚ) * (k : ℚ)) ∧
      ∀ y ∈ J', ∃ y'' ∈ J'', ∃ z ∈ Λ, ((N : ℤ) • y) * c = (N : ℤ) • y'' + (p : ℤ) • z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨φ, hφ1, hφmul, hφsurj, hφker⟩ :=
    QuaternionAlgebra.exists_linearMap_matrix_zmod_of_isMaximalOrder_of_ne hB Λ hΛ p hpq hpq'
  obtain ⟨h1', h2', h3', h4'⟩ := hJ'
  obtain ⟨h1'', h2'', h3'', h4''⟩ := hJ''
  set I' := lineSub φ hφmul hφsurj J' h2' h3' with hI'
  set I'' := lineSub φ hφmul hφsurj J'' h2'' h3'' with hI''
  obtain ⟨hne', hone'⟩ := image_ne_zero_and_ne_one hN0 hN hΛo J' h1' h2' h3' h4' hp hpN φ hφ1 hφker
  obtain ⟨hne'', hone''⟩ := image_ne_zero_and_ne_one hN0 hN hΛo J'' h1'' h2'' h3'' h4'' hp hpN φ hφ1 hφker
  have hI'0 : I' ≠ ⊥ := by
    obtain ⟨y, hy, h⟩ := hne'
    rw [Submodule.ne_bot_iff]
    exact ⟨_, (mem_lineSub φ hφmul hφsurj J' h2' h3' _).2 ⟨y, hy, rfl⟩, h⟩
  have hI'1 : I' ≠ ⊤ := by
    intro h
    have h1m : (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) ∈ I' := h ▸ Submodule.mem_top
    obtain ⟨y, hy, e⟩ := (mem_lineSub φ hφmul hφsurj J' h2' h3' _).1 h1m
    exact hone' y hy e.symm
  have hI''0 : I'' ≠ ⊥ := by
    obtain ⟨y, hy, h⟩ := hne''
    rw [Submodule.ne_bot_iff]
    exact ⟨_, (mem_lineSub φ hφmul hφsurj J'' h2'' h3'' _).2 ⟨y, hy, rfl⟩, h⟩
  have hI''1 : I'' ≠ ⊤ := by
    intro h
    have h1m : (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) ∈ I'' := h ▸ Submodule.mem_top
    obtain ⟨y, hy, e⟩ := (mem_lineSub φ hφmul hφsurj J'' h2'' h3'' _).1 h1m
    exact hone'' y hy e.symm
  obtain ⟨g, -, hg2, hg1, hmove⟩ := sl2Lines I' I'' hI'0 hI'1 hI''0 hI''1
  obtain ⟨c, hc⟩ := hφsurj g
  refine ⟨c, c.2, ?_, ?_⟩
  ·
    obtain ⟨⟨n, hn⟩, ⟨t, ht⟩⟩ := hΛo.exists_intCast_eq_nrd_and_exists_intCast_eq_trd c.2
    have hsq := mul_self_eq hn ht
    have hmem : (c : ℍ[ℚ, a, b]) * c ∈ Λ := hΛo.mul_mem c.2 c.2
    have hch : g * g = (t : ZMod p) • g - (n : ZMod p) • 1 := by
      have e1 : φ ⟨(c : ℍ[ℚ, a, b]) * c, hmem⟩ = g * g := by rw [hφmul c c hmem, hc]
      have e2 : (⟨(c : ℍ[ℚ, a, b]) * c, hmem⟩ : ↥Λ) = t • c - n • ⟨1, hΛo.one_mem⟩ :=
        Subtype.ext (by simpa using hsq)
      rw [← e1, e2, map_sub, map_zsmul, map_zsmul, hc, hφ1, ← Int.cast_smul_eq_zsmul (ZMod p) t,
        ← Int.cast_smul_eq_zsmul (ZMod p) n]
    have hn1 := cast_eq_one_of_unipotent hg2 hg1 hch
    have hdv : ((n - 1 : ℤ) : ZMod p) = 0 := by push_cast; rw [hn1, sub_self]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (n - 1) p).1 hdv
    refine ⟨k, ?_⟩
    rw [← hn]
    have : n = 1 + (p : ℤ) * k := by linarith
    exact_mod_cast this
  · intro y hy
    have hmemI : φ ⟨(N : ℤ) • y, h3' y hy⟩ * g ∈ I'' :=
      hmove _ ((mem_lineSub φ hφmul hφsurj J' h2' h3' _).2 ⟨y, hy, rfl⟩)
    obtain ⟨y'', hy'', e⟩ := (mem_lineSub φ hφmul hφsurj J'' h2'' h3'' _).1 hmemI
    have hmem2 : ((N : ℤ) • y) * (c : ℍ[ℚ, a, b]) ∈ Λ := hΛo.mul_mem (h3' y hy) c.2
    have e3 : φ ⟨((N : ℤ) • y) * (c : ℍ[ℚ, a, b]), hmem2⟩ = φ ⟨(N : ℤ) • y'', h3'' y'' hy''⟩ := by
      rw [hφmul ⟨(N : ℤ) • y, h3' y hy⟩ c hmem2, hc]; exact e
    have e4 : φ (⟨((N : ℤ) • y) * (c : ℍ[ℚ, a, b]), hmem2⟩ - ⟨(N : ℤ) • y'', h3'' y'' hy''⟩) = 0 := by
      rw [map_sub, e3, sub_self]
    obtain ⟨z, hz⟩ := (hφker _).1 e4
    have hz' : ((N : ℤ) • y) * (c : ℍ[ℚ, a, b]) - (N : ℤ) • y'' = (p : ℚ) • (z : ℍ[ℚ, a, b]) := hz
    refine ⟨y'', hy'', z, z.2, ?_⟩
    rw [natCast_zsmul_eq_ratCast_smul p, ← hz']; abel

end LevmodFinite

open LevmodFinite in
theorem solution
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hN : Squarefree N)
    (J' J'' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2)
    (hJ'' : Λ ≤ J'' ∧ (∀ x ∈ Λ, ∀ y ∈ J'', x * y ∈ J'') ∧ (∀ y ∈ J'', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J''.toAddSubgroup = N ^ 2) :
    ∃ c ∈ Λ, (∃ k : ℤ, nrd c = 1 + (N : ℚ) * (k : ℚ)) ∧ ∀ y ∈ J', y * c ∈ J'' := by
  classical
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hN0 : N ≠ 0 := NeZero.ne N

  have main : ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p ∣ N) →
      ∃ c ∈ Λ, (∃ k : ℤ, nrd c = 1 + ((∏ p ∈ S, p : ℕ) : ℚ) * (k : ℚ)) ∧
        ∀ y ∈ J', ∃ y'' ∈ J'', ∃ z ∈ Λ,
          ((N : ℤ) • y) * c = (N : ℤ) • y'' + ((∏ p ∈ S, p : ℕ) : ℤ) • z := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, hΛo.one_mem, ⟨0, by simp [nrd_one]⟩, fun y hy => ⟨0, zero_mem _, (N : ℤ) • y, hJ'.2.2.1 y hy, ?_⟩⟩
      simp
    | insert p S hpS ih =>
      intro hS
      obtain ⟨c', hc'Λ, ⟨k', hk'⟩, hmove'⟩ := ih (fun r hr => hS r (Finset.mem_insert_of_mem hr))
      obtain ⟨hp, hpN⟩ := hS p (Finset.mem_insert_self p S)
      have hpq : p ≠ q := by rintro rfl; exact hqN hpN
      have hpq' : p ≠ q' := by rintro rfl; exact hq'N hpN
      obtain ⟨cp, hcpΛ, ⟨kp, hkp⟩, hmovep⟩ := local_step hB Λ hΛ hN J' J'' hJ' hJ'' hp hpN hpq hpq'
      rw [Finset.prod_insert hpS]
      set M' : ℕ := ∏ r ∈ S, r with hM'
      have hcop : Nat.Coprime p M' := by
        refine Nat.Coprime.prod_right fun r hr => ?_
        have hrp := (hS r (Finset.mem_insert_of_mem hr)).1
        exact (Nat.coprime_primes hp hrp).mpr (fun h => hpS (h ▸ hr))
      have hcopZ : IsCoprime (p : ℤ) (M' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
      obtain ⟨α, β, hαβ⟩ := hcopZ
      refine ⟨(α * p) • c' + (β * M') • cp, add_mem (Λ.smul_mem _ hc'Λ) (Λ.smul_mem _ hcpΛ), ?_, ?_⟩
      · have e1 : (α * (p : ℤ)) • c' + (β * (M' : ℤ)) • cp = cp + (p : ℤ) • (α • (c' - cp)) := by
          have : β * (M' : ℤ) = 1 - α * p := by linarith
          rw [this]; module
        have e2 : (α * (p : ℤ)) • c' + (β * (M' : ℤ)) • cp = c' + (M' : ℤ) • (β • (cp - c')) := by
          have : α * (p : ℤ) = 1 - β * M' := by linarith
          rw [this]; module
        obtain ⟨j₁, hj₁⟩ := exists_nrd_add_zsmul hΛo hcpΛ (Λ.smul_mem α (sub_mem hc'Λ hcpΛ)) (p : ℤ)
        obtain ⟨j₂, hj₂⟩ := exists_nrd_add_zsmul hΛo hc'Λ (Λ.smul_mem β (sub_mem hcpΛ hc'Λ)) (M' : ℤ)
        obtain ⟨ν, hν⟩ := (hΛo.exists_intCast_eq_nrd_and_exists_intCast_eq_trd
          (add_mem (Λ.smul_mem (α * (p : ℤ)) hc'Λ) (Λ.smul_mem (β * (M' : ℤ)) hcpΛ))).1
        have hνp : (p : ℤ) ∣ ν - 1 := by
          refine ⟨kp + j₁, ?_⟩
          have h' : (ν : ℚ) = 1 + (p : ℚ) * ((kp + j₁ : ℤ) : ℚ) := by
            rw [hν, e1, hj₁, hkp]; push_cast; ring
          have h'' : ν = 1 + (p : ℤ) * (kp + j₁) := by exact_mod_cast h'
          linarith
        have hνM : (M' : ℤ) ∣ ν - 1 := by
          refine ⟨k' + j₂, ?_⟩
          have h' : (ν : ℚ) = 1 + (M' : ℚ) * ((k' + j₂ : ℤ) : ℚ) := by
            rw [hν, e2, hj₂, hk']; push_cast; ring
          have h'' : ν = 1 + (M' : ℤ) * (k' + j₂) := by exact_mod_cast h'
          linarith
        obtain ⟨k, hk⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).mul_dvd hνp hνM
        refine ⟨k, ?_⟩
        rw [← hν]
        have h'' : ν = 1 + (p : ℤ) * (M' : ℤ) * k := by linarith
        push_cast
        exact_mod_cast h''
      · intro y hy
        obtain ⟨y₁, hy₁, z₁, hz₁, e₁⟩ := hmove' y hy
        obtain ⟨y₂, hy₂, z₂, hz₂, e₂⟩ := hmovep y hy
        refine ⟨(α * p) • y₁ + (β * M') • y₂, add_mem (J''.smul_mem _ hy₁) (J''.smul_mem _ hy₂),
          α • z₁ + β • z₂, add_mem (Λ.smul_mem _ hz₁) (Λ.smul_mem _ hz₂), ?_⟩
        rw [mul_add, mul_smul_comm, mul_smul_comm, e₁, e₂]
        push_cast
        module
  obtain ⟨c, hcΛ, ⟨k, hk⟩, hmove⟩ :=
    main N.primeFactors (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩)
  have hprodN : (∏ p ∈ N.primeFactors, p) = N := Nat.prod_primeFactors_of_squarefree hN
  rw [hprodN] at hk hmove
  refine ⟨c, hcΛ, ⟨k, hk⟩, fun y hy => ?_⟩
  obtain ⟨y'', hy'', z, hz, e⟩ := hmove y hy
  have hyc : y * c = y'' + z := by
    apply zsmul_right_cancel (Int.natCast_ne_zero.mpr hN0)
    rw [smul_add, ← e, smul_mul_assoc]
  rw [hyc]
  exact add_mem hy'' (hJ''.1 hz)

end S_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mul_mem_of_levelModule
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_forall_mul_mem_of_levelModule (solution)
