-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/35812c2f-cc43-5480-9704-d1562c2464ec

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Quaternion

namespace WACC

section Generic

variable {K : Type*} [Field K] (𝒪 : Subring K) {a' b' : K}

theorem nrd_mul' (x y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem nrd_smul' (s : K) (x : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (s • x) = s ^ 2 * QuaternionAlgebra.nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, QuaternionAlgebra.nrd_mk, smul_eq_mul]
  ring

private def _root_.WACC.polar (x y : ℍ[K, a', b']) : K :=
  QuaternionAlgebra.nrd (x + y) - QuaternionAlgebra.nrd x - QuaternionAlgebra.nrd y

p2m_export "WACC" "polar"
theorem nrd_add (x y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (x + y) = QuaternionAlgebra.nrd x + polar x y + QuaternionAlgebra.nrd y := by
  simp only [polar]; ring

theorem polar_smul_right (x y : ℍ[K, a', b']) (s : K) : polar x (s • y) = s * polar x y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [polar, QuaternionAlgebra.smul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.nrd_mk,
    smul_eq_mul]
  ring

theorem polar_smul_left (x y : ℍ[K, a', b']) (s : K) : polar (s • x) y = s * polar x y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [polar, QuaternionAlgebra.smul_mk, QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.nrd_mk,
    smul_eq_mul]
  ring

theorem sq_eq_trd_smul_sub (y : ℍ[K, a', b']) :
    y * y = QuaternionAlgebra.trd y • y - QuaternionAlgebra.nrd y • (1 : ℍ[K, a', b']) := by
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  ext <;> simp [QuaternionAlgebra.nrd, QuaternionAlgebra.trd] <;> ring

theorem trd_eq (y : ℍ[K, a', b']) : QuaternionAlgebra.trd y = 2 * y.re := rfl

theorem nrd_one_add (y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (1 + y) = 1 + QuaternionAlgebra.trd y + QuaternionAlgebra.nrd y := by
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp [QuaternionAlgebra.nrd, QuaternionAlgebra.trd]
  ring

theorem nrd_one_sub (y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (1 - y) = 1 - QuaternionAlgebra.trd y + QuaternionAlgebra.nrd y := by
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp [QuaternionAlgebra.nrd, QuaternionAlgebra.trd]
  ring

noncomputable def cay (x : ℍ[K, a', b']) : ℍ[K, a', b'] := (QuaternionAlgebra.nrd x)⁻¹ • (x * x)

theorem nrd_cay {x : ℍ[K, a', b']} (hx : QuaternionAlgebra.nrd x ≠ 0) :
    QuaternionAlgebra.nrd (cay x) = 1 := by
  rw [cay, nrd_smul', nrd_mul']
  field_simp

theorem cay_one_add {y : ℍ[K, a', b']} (hy : QuaternionAlgebra.nrd y = 1)
    (ht : QuaternionAlgebra.nrd (1 + y) ≠ 0) : cay (1 + y) = y := by
  have hsq : (1 + y) * (1 + y) = QuaternionAlgebra.nrd (1 + y) • y := by
    rw [nrd_one_add, hy]
    have h2 := sq_eq_trd_smul_sub y
    rw [hy, one_smul] at h2
    calc (1 + y) * (1 + y) = 1 + (2 : K) • y + y * y := by
            simp only [mul_add, add_mul, one_mul, mul_one, two_smul]; abel
      _ = 1 + (2 : K) • y + (QuaternionAlgebra.trd y • y - 1) := by rw [h2]
      _ = (1 + QuaternionAlgebra.trd y + 1) • y := by
            rw [add_smul, add_smul, one_smul]; module
  rw [cay, hsq, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem cay_one_sub {y : ℍ[K, a', b']} (hy : QuaternionAlgebra.nrd y = 1)
    (ht : QuaternionAlgebra.nrd (1 - y) ≠ 0) : cay (1 - y) = -y := by
  have hsq : (1 - y) * (1 - y) = QuaternionAlgebra.nrd (1 - y) • (-y) := by
    rw [nrd_one_sub, hy]
    have h2 := sq_eq_trd_smul_sub y
    rw [hy, one_smul] at h2
    calc (1 - y) * (1 - y) = 1 - (2 : K) • y + y * y := by
            simp only [mul_sub, sub_mul, one_mul, mul_one, two_smul]; abel
      _ = 1 - (2 : K) • y + (QuaternionAlgebra.trd y • y - 1) := by rw [h2]
      _ = (1 - QuaternionAlgebra.trd y + 1) • (-y) := by
            rw [smul_neg, add_smul, sub_smul, one_smul]; module
  rw [cay, hsq, smul_smul, inv_mul_cancel₀ ht, one_smul]

theorem cay_i (ha : a' ≠ 0) : cay (⟨0, 1, 0, 0⟩ : ℍ[K, a', b']) = -1 := by
  rw [cay]
  have hn : QuaternionAlgebra.nrd (⟨0, 1, 0, 0⟩ : ℍ[K, a', b']) = -a' := by
    simp [QuaternionAlgebra.nrd]
  rw [hn]
  ext <;> simp <;> field_simp

def IsInt (q : ℍ[K, a', b']) : Prop := q.re ∈ 𝒪 ∧ q.imI ∈ 𝒪 ∧ q.imJ ∈ 𝒪 ∧ q.imK ∈ 𝒪

variable {𝒪}

theorem IsInt.add {q r : ℍ[K, a', b']} (hq : IsInt 𝒪 q) (hr : IsInt 𝒪 r) : IsInt 𝒪 (q + r) :=
  ⟨𝒪.add_mem hq.1 hr.1, 𝒪.add_mem hq.2.1 hr.2.1, 𝒪.add_mem hq.2.2.1 hr.2.2.1, 𝒪.add_mem hq.2.2.2 hr.2.2.2⟩

theorem IsInt.sub {q r : ℍ[K, a', b']} (hq : IsInt 𝒪 q) (hr : IsInt 𝒪 r) : IsInt 𝒪 (q - r) :=
  ⟨𝒪.sub_mem hq.1 hr.1, 𝒪.sub_mem hq.2.1 hr.2.1, 𝒪.sub_mem hq.2.2.1 hr.2.2.1, 𝒪.sub_mem hq.2.2.2 hr.2.2.2⟩

theorem IsInt.neg {q : ℍ[K, a', b']} (hq : IsInt 𝒪 q) : IsInt 𝒪 (-q) :=
  ⟨𝒪.neg_mem hq.1, 𝒪.neg_mem hq.2.1, 𝒪.neg_mem hq.2.2.1, 𝒪.neg_mem hq.2.2.2⟩

theorem isInt_zero : IsInt 𝒪 (0 : ℍ[K, a', b']) :=
  ⟨𝒪.zero_mem, 𝒪.zero_mem, 𝒪.zero_mem, 𝒪.zero_mem⟩

theorem isInt_one : IsInt 𝒪 (1 : ℍ[K, a', b']) :=
  ⟨𝒪.one_mem, 𝒪.zero_mem, 𝒪.zero_mem, 𝒪.zero_mem⟩

theorem IsInt.smul {q : ℍ[K, a', b']} {c : K} (hc : c ∈ 𝒪) (hq : IsInt 𝒪 q) : IsInt 𝒪 (c • q) := by
  obtain ⟨q₀, q₁, q₂, q₃⟩ := q
  obtain ⟨h0, h1, h2, h3⟩ := hq
  exact ⟨𝒪.mul_mem hc h0, 𝒪.mul_mem hc h1, 𝒪.mul_mem hc h2, 𝒪.mul_mem hc h3⟩

theorem natCast_mem' (n : ℕ) : (n : K) ∈ 𝒪 := natCast_mem 𝒪 n

theorem IsInt.natCast_smul {q : ℍ[K, a', b']} (n : ℕ) (hq : IsInt 𝒪 q) : IsInt 𝒪 ((n : K) • q) :=
  hq.smul (natCast_mem' n)

theorem IsInt.mul {A : ℕ} (hA : (A : K) * a' ∈ 𝒪) (hB : (A : K) * b' ∈ 𝒪)
    {q r : ℍ[K, a', b']} (hq : IsInt 𝒪 q) (hr : IsInt 𝒪 r) :
    IsInt 𝒪 (((A : K) ^ 2) • (q * r)) := by
  obtain ⟨q₀, q₁, q₂, q₃⟩ := q
  obtain ⟨r₀, r₁, r₂, r₃⟩ := r
  obtain ⟨h0, h1, h2, h3⟩ := hq
  obtain ⟨k0, k1, k2, k3⟩ := hr
  simp only at h0 h1 h2 h3 k0 k1 k2 k3
  have hAA : (A : K) ∈ 𝒪 := natCast_mem' A
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.smul_mk, smul_eq_mul, zero_mul,
      mul_zero, add_zero, sub_zero]
  · have e : (A : K) ^ 2 * (q₀ * r₀ + a' * q₁ * r₁ + b' * q₂ * r₂ - a' * b' * q₃ * r₃)
        = (A : K) * (A : K) * (q₀ * r₀) + (A : K) * ((A : K) * a') * (q₁ * r₁)
          + (A : K) * ((A : K) * b') * (q₂ * r₂) - ((A : K) * a') * ((A : K) * b') * (q₃ * r₃) := by ring
    rw [e]
    apply_rules [Subring.add_mem, Subring.sub_mem, Subring.mul_mem]
  · have e : (A : K) ^ 2 * (q₀ * r₁ + q₁ * r₀ - b' * q₂ * r₃ + b' * q₃ * r₂)
        = (A : K) * (A : K) * (q₀ * r₁) + (A : K) * (A : K) * (q₁ * r₀)
          - (A : K) * ((A : K) * b') * (q₂ * r₃) + (A : K) * ((A : K) * b') * (q₃ * r₂) := by ring
    rw [e]
    apply_rules [Subring.add_mem, Subring.sub_mem, Subring.mul_mem]
  · have e : (A : K) ^ 2 * (q₀ * r₂ + a' * q₁ * r₃ + q₂ * r₀ - a' * q₃ * r₁)
        = (A : K) * (A : K) * (q₀ * r₂) + (A : K) * ((A : K) * a') * (q₁ * r₃)
          + (A : K) * (A : K) * (q₂ * r₀) - (A : K) * ((A : K) * a') * (q₃ * r₁) := by ring
    rw [e]
    apply_rules [Subring.add_mem, Subring.sub_mem, Subring.mul_mem]
  · have e : (A : K) ^ 2 * (q₀ * r₃ + q₁ * r₂ - q₂ * r₁ + q₃ * r₀)
        = (A : K) * (A : K) * (q₀ * r₃) + (A : K) * (A : K) * (q₁ * r₂)
          - (A : K) * (A : K) * (q₂ * r₁) + (A : K) * (A : K) * (q₃ * r₀) := by ring
    rw [e]
    apply_rules [Subring.add_mem, Subring.sub_mem, Subring.mul_mem]

theorem IsInt.nrd {A : ℕ} (hA : (A : K) * a' ∈ 𝒪) (hB : (A : K) * b' ∈ 𝒪)
    {q : ℍ[K, a', b']} (hq : IsInt 𝒪 q) : (A : K) ^ 2 * QuaternionAlgebra.nrd q ∈ 𝒪 := by
  obtain ⟨q₀, q₁, q₂, q₃⟩ := q
  obtain ⟨h0, h1, h2, h3⟩ := hq
  simp only at h0 h1 h2 h3
  have hAA : (A : K) ∈ 𝒪 := natCast_mem' A
  rw [QuaternionAlgebra.nrd_mk]
  have e : (A : K) ^ 2 * (q₀ ^ 2 - a' * q₁ ^ 2 - b' * q₂ ^ 2 + a' * b' * q₃ ^ 2)
      = (A : K) * (A : K) * (q₀ * q₀) - (A : K) * ((A : K) * a') * (q₁ * q₁)
        - (A : K) * ((A : K) * b') * (q₂ * q₂) + ((A : K) * a') * ((A : K) * b') * (q₃ * q₃) := by ring
  rw [e]
  apply_rules [Subring.add_mem, Subring.sub_mem, Subring.mul_mem]

theorem IsInt.polar {A : ℕ} (hA : (A : K) * a' ∈ 𝒪) (hB : (A : K) * b' ∈ 𝒪)
    {q r : ℍ[K, a', b']} (hq : IsInt 𝒪 q) (hr : IsInt 𝒪 r) : (A : K) ^ 2 * polar q r ∈ 𝒪 := by
  rw [WACC.polar, mul_sub, mul_sub]
  exact 𝒪.sub_mem (𝒪.sub_mem ((hq.add hr).nrd hA hB) (hq.nrd hA hB)) (hr.nrd hA hB)

theorem lin4 {κ₁ κ₂ κ₃ κ₄ μ₁ μ₂ μ₃ μ₄ : K} (m₁ m₂ m₃ m₄ : ℍ[K, a', b'])
    (h₁ : κ₁ = μ₁) (h₂ : κ₂ = μ₂) (h₃ : κ₃ = μ₃) (h₄ : κ₄ = μ₄) :
    κ₁ • m₁ + κ₂ • m₂ + κ₃ • m₃ + κ₄ • m₄ = μ₁ • m₁ + μ₂ • m₂ + μ₃ • m₃ + μ₄ • m₄ := by
  rw [h₁, h₂, h₃, h₄]

theorem cay_estimate {A : ℕ} (hA : (A : K) * a' ∈ 𝒪) (hB : (A : K) * b' ∈ 𝒪)
    (ϖ : K) (hϖ : ϖ ∈ 𝒪) (hunit : ∀ c ∈ 𝒪, ∃ c' ∈ 𝒪, (1 + ϖ * c) * c' = 1)
    (d h : ℕ) (hd : (d : K) ≠ 0)
    (x₀ : ℍ[K, a', b']) (hx₀ : IsInt 𝒪 ((d : K) • x₀)) (hn₀ : QuaternionAlgebra.nrd x₀ ≠ 0)
    (hh : (h : K) * (QuaternionAlgebra.nrd x₀)⁻¹ ∈ 𝒪)
    (M' : K) (hM' : M' ∈ 𝒪) (r : ℍ[K, a', b']) (hr : IsInt 𝒪 r) :
    QuaternionAlgebra.nrd (x₀ + (M' * ϖ * (h : K) ^ 2 * (d : K) ^ 4 * (A : K) ^ 4) • r) ≠ 0 ∧
    ∃ q : ℍ[K, a', b'], IsInt 𝒪 q ∧
      cay (x₀ + (M' * ϖ * (h : K) ^ 2 * (d : K) ^ 4 * (A : K) ^ 4) • r) - cay x₀ = M' • q := by

  set n₀ := QuaternionAlgebra.nrd x₀ with hn₀def
  set L : K := M' * ϖ * (h : K) ^ 2 * (d : K) ^ 4 * (A : K) ^ 4 with hL
  set X₀ : ℍ[K, a', b'] := (d : K) • x₀ with hX₀
  have hAA : (A : K) ∈ 𝒪 := natCast_mem' A
  have hdd : (d : K) ∈ 𝒪 := natCast_mem' d
  have hhh : (h : K) ∈ 𝒪 := natCast_mem' h
  have hLmem : L ∈ 𝒪 := by
    rw [hL]; apply_rules [Subring.mul_mem, Subring.pow_mem]
  have hx₀X : x₀ = (d : K)⁻¹ • X₀ := by rw [hX₀, smul_smul, inv_mul_cancel₀ hd, one_smul]

  set δ₁ : K := polar x₀ r + L * QuaternionAlgebra.nrd r with hδ₁
  have hn : QuaternionAlgebra.nrd (x₀ + L • r) = n₀ + L * δ₁ := by
    rw [nrd_add, polar_smul_right, nrd_smul', hδ₁]; ring

  have hδ₁' : (d : K) ^ 2 * (A : K) ^ 2 * δ₁ ∈ 𝒪 := by
    have h1 : (A : K) ^ 2 * polar X₀ r ∈ 𝒪 := hx₀.polar hA hB hr
    have h2 : (A : K) ^ 2 * QuaternionAlgebra.nrd r ∈ 𝒪 := hr.nrd hA hB
    have e : (d : K) ^ 2 * (A : K) ^ 2 * δ₁
        = (d : K) * ((A : K) ^ 2 * polar X₀ r) + (d : K) * (d : K) * L * ((A : K) ^ 2 * QuaternionAlgebra.nrd r) := by
      rw [hδ₁, hX₀, polar_smul_left]; ring
    rw [e]
    apply_rules [Subring.add_mem, Subring.mul_mem]

  set c : K := M' * ((h : K) * n₀⁻¹) * (h : K) * ((d : K) ^ 2 * (A : K) ^ 2)
      * ((d : K) ^ 2 * (A : K) ^ 2 * δ₁) with hc
  have hcmem : c ∈ 𝒪 := by
    rw [hc]; apply_rules [Subring.mul_mem, Subring.pow_mem]
  have hLδ : L * δ₁ = n₀ * (ϖ * c) := by
    rw [hL, hc]; field_simp
  obtain ⟨c', hc'mem, hcc'⟩ := hunit c hcmem
  have hunit0 : 1 + ϖ * c ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hcc'; exact zero_ne_one hcc'
  have hn' : QuaternionAlgebra.nrd (x₀ + L • r) = n₀ * (1 + ϖ * c) := by rw [hn, hLδ]; ring
  have hnz : QuaternionAlgebra.nrd (x₀ + L • r) ≠ 0 := by
    rw [hn']; exact mul_ne_zero hn₀ hunit0
  refine ⟨hnz, ?_⟩
  have hninv : (QuaternionAlgebra.nrd (x₀ + L • r))⁻¹ = n₀⁻¹ * c' := by
    rw [hn', mul_inv, inv_eq_of_mul_eq_one_right hcc']

  set D' : ℍ[K, a', b'] := ((A : K) ^ 2) • (X₀ * r) + ((A : K) ^ 2) • (r * X₀)
      + ((d : K) * L) • (((A : K) ^ 2) • (r * r)) with hD'
  have hD'int : IsInt 𝒪 D' := by
    rw [hD']
    exact ((hx₀.mul hA hB hr).add (hr.mul hA hB hx₀)).add ((hr.mul hA hB hr).smul (𝒪.mul_mem hdd hLmem))
  set α : K := -(ϖ * c' * ((h : K) * n₀⁻¹) ^ 2 * ((d : K) ^ 2 * (A : K) ^ 2 * δ₁)) with hα
  set β : K := c' * ϖ * ((h : K) * n₀⁻¹) * (h : K) * (d : K) ^ 3 * (A : K) ^ 2 with hβ
  have hαmem : α ∈ 𝒪 := by rw [hα]; apply_rules [Subring.neg_mem, Subring.mul_mem, Subring.pow_mem]
  have hβmem : β ∈ 𝒪 := by rw [hβ]; apply_rules [Subring.mul_mem, Subring.pow_mem]
  refine ⟨α • (((A : K) ^ 2) • (X₀ * X₀)) + β • D', ?_, ?_⟩
  · exact ((hx₀.mul hA hB hx₀).smul hαmem).add (hD'int.smul hβmem)

  have lhs : cay (x₀ + L • r) - cay x₀
      = (n₀⁻¹ * c' * (d : K)⁻¹ ^ 2 - n₀⁻¹ * (d : K)⁻¹ ^ 2) • (X₀ * X₀)
        + (n₀⁻¹ * c' * (d : K)⁻¹ * L) • (X₀ * r) + (n₀⁻¹ * c' * L * (d : K)⁻¹) • (r * X₀)
        + (n₀⁻¹ * c' * L * L) • (r * r) := by
    rw [cay, cay, hninv, ← hn₀def, hx₀X]
    simp only [mul_add, add_mul, smul_mul_smul_comm, smul_add, smul_smul]
    module
  have rhs : M' • (α • (((A : K) ^ 2) • (X₀ * X₀)) + β • D')
      = (M' * α * (A : K) ^ 2) • (X₀ * X₀) + (M' * β * (A : K) ^ 2) • (X₀ * r)
        + (M' * β * (A : K) ^ 2) • (r * X₀) + (M' * β * ((d : K) * L) * (A : K) ^ 2) • (r * r) := by
    rw [hD']
    simp only [smul_add, smul_smul]
    module
  rw [lhs, rhs]
  apply lin4
  · rw [hα]
    have e : c' - 1 = -(ϖ * c * c') := by linear_combination hcc'
    have : n₀⁻¹ * c' * (d : K)⁻¹ ^ 2 - n₀⁻¹ * (d : K)⁻¹ ^ 2 = n₀⁻¹ * (d : K)⁻¹ ^ 2 * (c' - 1) := by ring
    rw [this, e, hc]
    field_simp
  · rw [hβ, hL]; field_simp
  · rw [hβ, hL]; field_simp
  · rw [hβ, hL]; field_simp

end Generic

end WACC

namespace WACC

open IsDedekindDomain NumberField
open scoped TensorProduct

section Places

noncomputable abbrev pgen (w : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.natGenerator w

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ pgen w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem asIdeal_eq_span_pgen (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.asIdeal = Ideal.span {((pgen w : ℕ) : 𝓞 ℚ)} := by
  set e := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) w
  have h1 : w.asIdeal = (w.asIdeal.map e).comap e := (Ideal.comap_map_of_bijective e e.bijective).symm
  rw [h1, ← h, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
  congr 2
  simp [e]

theorem valuation_pgen (w : HeightOneSpectrum (𝓞 ℚ)) :
    w.valuation ℚ ((pgen w : ℕ) : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [show ((pgen w : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((pgen w : ℕ) : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  refine HeightOneSpectrum.intValuation_singleton w ?_ (asIdeal_eq_span_pgen w)
  exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem valued_pgen_pow (w : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    Valued.v (((pgen w : ℕ) : w.adicCompletion ℚ) ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, show ((pgen w : ℕ) : w.adicCompletion ℚ) = algebraMap ℚ (w.adicCompletion ℚ) ((pgen w : ℕ) : ℚ)
    from (map_natCast _ _).symm, valued_algebraMap, valuation_pgen, ← WithZero.exp_nsmul]
  simp

theorem pgen_injective {w w' : HeightOneSpectrum (𝓞 ℚ)} (h : pgen w = pgen w') : w = w' := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

noncomputable abbrev Ow (w : HeightOneSpectrum (𝓞 ℚ)) : Subring (w.adicCompletion ℚ) :=
  (w.adicCompletionIntegers ℚ).toSubring

theorem mem_Ow_iff (w : HeightOneSpectrum (𝓞 ℚ)) (x : w.adicCompletion ℚ) :
    x ∈ Ow w ↔ Valued.v x ≤ 1 := HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

theorem hunit_pgen (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ c ∈ Ow w, ∃ c' ∈ Ow w, (1 + ((pgen w : ℕ) : w.adicCompletion ℚ) * c) * c' = 1 := by
  intro c hc
  rw [mem_Ow_iff] at hc
  set u : w.adicCompletion ℚ := 1 + ((pgen w : ℕ) : w.adicCompletion ℚ) * c with hu
  have hpc : Valued.v (((pgen w : ℕ) : w.adicCompletion ℚ) * c) < 1 := by
    rw [map_mul, ← pow_one ((pgen w : ℕ) : w.adicCompletion ℚ), valued_pgen_pow]
    calc WithZero.exp (-((1 : ℕ) : ℤ)) * Valued.v c ≤ WithZero.exp (-((1 : ℕ) : ℤ)) * 1 :=
          mul_le_mul_right hc _
      _ < 1 := by
          rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hvu : Valued.v u = 1 := by
    rw [hu, Valuation.map_add_eq_of_lt_left]
    · exact map_one _
    · rw [map_one]; exact hpc
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvu; exact zero_ne_one hvu
  refine ⟨u⁻¹, ?_, mul_inv_cancel₀ hu0⟩
  rw [mem_Ow_iff, map_inv₀, hvu, inv_one]

theorem exists_pgen_pow_mul_mem (w : HeightOneSpectrum (𝓞 ℚ)) (e : w.adicCompletion ℚ) :
    ∃ k : ℕ, ((pgen w : ℕ) : w.adicCompletion ℚ) ^ k * e ∈ Ow w := by
  by_cases he : e = 0
  · exact ⟨0, by rw [he, mul_zero]; exact (Ow w).zero_mem⟩
  · set m : ℤ := WithZero.log (Valued.v e) with hm
    have hve : Valued.v e = WithZero.exp m := (WithZero.exp_log ((Valuation.ne_zero_iff _).2 he)).symm
    refine ⟨m.toNat, ?_⟩
    rw [mem_Ow_iff, map_mul, valued_pgen_pow, hve, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    have := Int.self_le_toNat m
    omega

theorem pgen_pow_mul_mem_mono (w : HeightOneSpectrum (𝓞 ℚ)) {e : w.adicCompletion ℚ} {k : ℕ}
    (hk : ((pgen w : ℕ) : w.adicCompletion ℚ) ^ k * e ∈ Ow w) (j : ℕ) :
    ((pgen w : ℕ) : w.adicCompletion ℚ) ^ (k + j) * e ∈ Ow w := by
  rw [pow_add, mul_comm (_ ^ k), mul_assoc]
  exact (Ow w).mul_mem ((Ow w).pow_mem (natCast_mem _ _) _) hk

theorem natCast_mul_mem_of_dvd (w : HeightOneSpectrum (𝓞 ℚ)) {e : w.adicCompletion ℚ} {k n : ℕ}
    (hk : ((pgen w : ℕ) : w.adicCompletion ℚ) ^ k * e ∈ Ow w) (hn : pgen w ^ k ∣ n) :
    (n : w.adicCompletion ℚ) * e ∈ Ow w := by
  obtain ⟨m, rfl⟩ := hn
  rw [Nat.cast_mul, Nat.cast_pow, mul_comm (_ ^ k) (m : w.adicCompletion ℚ), mul_assoc]
  exact (Ow w).mul_mem (natCast_mem _ _) hk

theorem natCast_adicCompletion_ne_zero (w : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (hn : n ≠ 0) :
    (n : w.adicCompletion ℚ) ≠ 0 := by
  rw [show (n : w.adicCompletion ℚ) = algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) from (map_natCast _ _).symm]
  exact (map_ne_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective).2 (Nat.cast_ne_zero.2 hn)

theorem exists_rat_approx (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ρ : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ) (L : ℕ) (hL : L ≠ 0) :
    ∃ r : ℚ, ∀ w ∈ T, ∃ c ∈ Ow w,
      algebraMap ℚ (w.adicCompletion ℚ) r = ρ w + (L : w.adicCompletion ℚ) * c := by
  classical
  let f : (v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ :=
    fun v => if v ∈ T then ((L : v.adicCompletion ℚ))⁻¹ * ρ v else 0
  have hf : ∀ᶠ v in Filter.cofinite, f v ∈ v.adicCompletionIntegers ℚ := by
    rw [Filter.eventually_cofinite]
    refine (T.finite_toSet).subset ?_
    intro v hv
    by_contra hvT
    apply hv
    simp only [f, Finset.mem_coe.not.1 hvT, if_false]
    exact (v.adicCompletionIntegers ℚ).zero_mem
  let α : FiniteAdeleRing (𝓞 ℚ) ℚ := ⟨f, hf⟩
  obtain ⟨x, hx⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers ℚ α
  refine ⟨L * x, fun w hw => ?_⟩
  have hLw : (L : w.adicCompletion ℚ) ≠ 0 := natCast_adicCompletion_ne_zero w hL
  refine ⟨-(α w - algebraMap ℚ (w.adicCompletion ℚ) x), (Ow w).neg_mem (hx w), ?_⟩
  have hαw : α w = ((L : w.adicCompletion ℚ))⁻¹ * ρ w := by
    show f w = _
    simp only [f, hw, if_true]
  rw [hαw, map_mul, map_natCast]
  field_simp
  ring

end Places

end WACC

namespace WACC

open IsDedekindDomain NumberField
open scoped TensorProduct

section Hat

variable {a b : ℚ}

noncomputable abbrev cst (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) : w.adicCompletion ℚ :=
  algebraMap ℚ (w.adicCompletion ℚ) q

noncomputable def hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) :
    ℍ[w.adicCompletion ℚ, cst w a, cst w b] :=
  ⟨cst w x.re, cst w x.imI, cst w x.imJ, cst w x.imK⟩

@[scoped simp] theorem hatQ_re (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : (hatQ w x).re = cst w x.re := rfl
@[scoped simp] theorem hatQ_imI (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : (hatQ w x).imI = cst w x.imI := rfl
@[scoped simp] theorem hatQ_imJ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : (hatQ w x).imJ = cst w x.imJ := rfl
@[scoped simp] theorem hatQ_imK (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : (hatQ w x).imK = cst w x.imK := rfl

theorem hatQ_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b]) :
    hatQ w (x * y) = hatQ w x * hatQ w y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  ext <;> simp [hatQ, map_add, map_sub, map_mul]

theorem hatQ_add (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b]) :
    hatQ w (x + y) = hatQ w x + hatQ w y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  ext <;> simp [hatQ, map_add]

theorem hatQ_sub (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b]) :
    hatQ w (x - y) = hatQ w x - hatQ w y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  ext <;> simp [hatQ, map_sub]

theorem hatQ_neg (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) : hatQ w (-x) = -hatQ w x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [hatQ, map_neg]

theorem hatQ_smul (w : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) (x : ℍ[ℚ, a, b]) :
    hatQ w (q • x) = cst w q • hatQ w x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  ext <;> simp [hatQ, map_mul]

theorem hatQ_one (w : HeightOneSpectrum (𝓞 ℚ)) : hatQ w (1 : ℍ[ℚ, a, b]) = 1 := by
  ext <;> simp [hatQ]

theorem hatQ_mk (w : HeightOneSpectrum (𝓞 ℚ)) (x₀ x₁ x₂ x₃ : ℚ) :
    hatQ w (⟨x₀, x₁, x₂, x₃⟩ : ℍ[ℚ, a, b]) = ⟨cst w x₀, cst w x₁, cst w x₂, cst w x₃⟩ := rfl

theorem nrd_hatQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) :
    QuaternionAlgebra.nrd (hatQ w x) = cst w (QuaternionAlgebra.nrd x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [hatQ, QuaternionAlgebra.nrd, map_add, map_sub, map_mul, map_pow]

noncomputable def cayQ (x : ℍ[ℚ, a, b]) : ℍ[ℚ, a, b] := (QuaternionAlgebra.nrd x)⁻¹ • (x * x)

theorem nrd_cayQ {x : ℍ[ℚ, a, b]} (hx : QuaternionAlgebra.nrd x ≠ 0) :
    QuaternionAlgebra.nrd (cayQ x) = 1 := by
  have h1 : QuaternionAlgebra.nrd (x * x) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd x := by
    obtain ⟨x₀, x₁, x₂, x₃⟩ := x
    simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]; ring
  have h2 : ∀ (s : ℚ) (y : ℍ[ℚ, a, b]), QuaternionAlgebra.nrd (s • y) = s ^ 2 * QuaternionAlgebra.nrd y := by
    intro s y
    obtain ⟨y₀, y₁, y₂, y₃⟩ := y
    simp only [QuaternionAlgebra.smul_mk, QuaternionAlgebra.nrd_mk, smul_eq_mul]; ring
  rw [cayQ, h2, h1]
  field_simp

theorem hatQ_cayQ (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b]) :
    hatQ w (cayQ x) = cay (hatQ w x) := by
  rw [cayQ, cay, hatQ_smul, hatQ_mul, nrd_hatQ,
    show cst w (QuaternionAlgebra.nrd x)⁻¹ = (cst w (QuaternionAlgebra.nrd x))⁻¹ from map_inv₀ _ _]

theorem nrd_neg' {K : Type*} [CommRing K] {c₁ c₃ : K} (x : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (-x) = QuaternionAlgebra.nrd x := QuaternionAlgebra.nrd_neg x

end Hat

section Core

variable {a b : ℚ}

theorem exists_den (a b : ℚ) : ∃ A : ℕ, A ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ),
    (A : w.adicCompletion ℚ) * cst w a ∈ Ow w ∧ (A : w.adicCompletion ℚ) * cst w b ∈ Ow w := by
  refine ⟨a.den * b.den, mul_ne_zero a.den_ne_zero b.den_ne_zero, fun w => ⟨?_, ?_⟩⟩
  · have e : ((a.den * b.den : ℕ) : w.adicCompletion ℚ) * cst w a = ((b.den * a.num : ℤ) : w.adicCompletion ℚ) := by
      rw [show ((a.den * b.den : ℕ) : w.adicCompletion ℚ) = cst w ((a.den * b.den : ℕ) : ℚ) from
        (map_natCast _ _).symm, ← map_mul,
        show ((b.den * a.num : ℤ) : w.adicCompletion ℚ) = cst w ((b.den * a.num : ℤ) : ℚ) from
        (map_intCast _ _).symm]
      congr 1
      push_cast
      have := Rat.den_mul_eq_num a
      linear_combination (b.den : ℚ) * this
    rw [e]; exact intCast_mem _ _
  · have e : ((a.den * b.den : ℕ) : w.adicCompletion ℚ) * cst w b = ((a.den * b.num : ℤ) : w.adicCompletion ℚ) := by
      rw [show ((a.den * b.den : ℕ) : w.adicCompletion ℚ) = cst w ((a.den * b.den : ℕ) : ℚ) from
        (map_natCast _ _).symm, ← map_mul,
        show ((a.den * b.num : ℤ) : w.adicCompletion ℚ) = cst w ((a.den * b.num : ℤ) : ℚ) from
        (map_intCast _ _).symm]
      congr 1
      push_cast
      have := Rat.den_mul_eq_num b
      linear_combination (a.den : ℚ) * this
    rw [e]; exact intCast_mem _ _

theorem exists_exp_clear (w : HeightOneSpectrum (𝓞 ℚ))
    (ξ : ℍ[w.adicCompletion ℚ, cst w a, cst w b]) :
    ∃ k : ℕ, IsInt (Ow w) ((((pgen w : ℕ) : w.adicCompletion ℚ) ^ k) • ξ) ∧
      ((pgen w : ℕ) : w.adicCompletion ℚ) ^ k * (QuaternionAlgebra.nrd ξ)⁻¹ ∈ Ow w := by
  obtain ⟨k₀, h₀⟩ := exists_pgen_pow_mul_mem w ξ.re
  obtain ⟨k₁, h₁⟩ := exists_pgen_pow_mul_mem w ξ.imI
  obtain ⟨k₂, h₂⟩ := exists_pgen_pow_mul_mem w ξ.imJ
  obtain ⟨k₃, h₃⟩ := exists_pgen_pow_mul_mem w ξ.imK
  obtain ⟨k₄, h₄⟩ := exists_pgen_pow_mul_mem w (QuaternionAlgebra.nrd ξ)⁻¹
  refine ⟨k₀ + k₁ + k₂ + k₃ + k₄, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have := pgen_pow_mul_mem_mono w h₀ (k₁ + k₂ + k₃ + k₄)
    obtain ⟨ξ₀, ξ₁, ξ₂, ξ₃⟩ := ξ
    simpa [add_assoc] using this
  · have := pgen_pow_mul_mem_mono w h₁ (k₀ + k₂ + k₃ + k₄)
    obtain ⟨ξ₀, ξ₁, ξ₂, ξ₃⟩ := ξ
    simp only [QuaternionAlgebra.smul_mk, smul_eq_mul]
    convert this using 2; ring
  · have := pgen_pow_mul_mem_mono w h₂ (k₀ + k₁ + k₃ + k₄)
    obtain ⟨ξ₀, ξ₁, ξ₂, ξ₃⟩ := ξ
    simp only [QuaternionAlgebra.smul_mk, smul_eq_mul]
    convert this using 2; ring
  · have := pgen_pow_mul_mem_mono w h₃ (k₀ + k₁ + k₂ + k₄)
    obtain ⟨ξ₀, ξ₁, ξ₂, ξ₃⟩ := ξ
    simp only [QuaternionAlgebra.smul_mk, smul_eq_mul]
    convert this using 2; ring
  · have := pgen_pow_mul_mem_mono w h₄ (k₀ + k₁ + k₂ + k₃)
    convert this using 2; ring

theorem exists_nat_clear (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ξ : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[w.adicCompletion ℚ, cst w a, cst w b]) :
    ∃ N₀ : ℕ, N₀ ≠ 0 ∧ ∀ w ∈ T, IsInt (Ow w) ((N₀ : w.adicCompletion ℚ) • ξ w) ∧
      (N₀ : w.adicCompletion ℚ) * (QuaternionAlgebra.nrd (ξ w))⁻¹ ∈ Ow w := by
  classical
  choose k hk using fun w => exists_exp_clear w (ξ w)
  refine ⟨∏ w ∈ T, pgen w ^ k w, ?_, fun w hw => ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero
  have hdvd : pgen w ^ k w ∣ ∏ w ∈ T, pgen w ^ k w := Finset.dvd_prod_of_mem _ hw
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨?_, ?_⟩
  · have hint := (hk w).1
    have e : ((∏ w ∈ T, pgen w ^ k w : ℕ) : w.adicCompletion ℚ) • ξ w
        = (m : w.adicCompletion ℚ) • ((((pgen w : ℕ) : w.adicCompletion ℚ) ^ k w) • ξ w) := by
      rw [hm, smul_smul]; push_cast; rw [mul_comm]
    rw [e]
    exact hint.natCast_smul m
  · exact natCast_mul_mem_of_dvd w (hk w).2 ⟨m, hm⟩

theorem core_approx (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (hT : T.Nonempty)
    (ξ : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[w.adicCompletion ℚ, cst w a, cst w b])
    (hξ : ∀ w ∈ T, QuaternionAlgebra.nrd (ξ w) ≠ 0) (M₁ : ℕ) (hM₁ : M₁ ≠ 0) :
    ∃ x : ℍ[ℚ, a, b], QuaternionAlgebra.nrd x ≠ 0 ∧
      ∀ w ∈ T, ∃ q : ℍ[w.adicCompletion ℚ, cst w a, cst w b], IsInt (Ow w) q ∧
        cay (hatQ w x) - cay (ξ w) = (M₁ : w.adicCompletion ℚ) • q := by
  classical
  obtain ⟨A, hA0, hA⟩ := exists_den a b
  obtain ⟨N₀, hN₀, hN⟩ := exists_nat_clear T ξ

  set P : ℕ := ∏ w ∈ T, pgen w with hP
  set L : ℕ := M₁ * P * N₀ ^ 2 * N₀ ^ 4 * A ^ 4 with hL
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => (Rat.HeightOneSpectrum.prime_natGenerator w).ne_zero
  have hL0 : L ≠ 0 := by
    rw [hL]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hM₁ hP0) (pow_ne_zero _ hN₀))
      (pow_ne_zero _ hN₀)) (pow_ne_zero _ hA0)

  obtain ⟨r₀, hr₀⟩ := exists_rat_approx T (fun w => (ξ w).re) L hL0
  obtain ⟨r₁, hr₁⟩ := exists_rat_approx T (fun w => (ξ w).imI) L hL0
  obtain ⟨r₂, hr₂⟩ := exists_rat_approx T (fun w => (ξ w).imJ) L hL0
  obtain ⟨r₃, hr₃⟩ := exists_rat_approx T (fun w => (ξ w).imK) L hL0
  set x : ℍ[ℚ, a, b] := ⟨r₀, r₁, r₂, r₃⟩ with hx

  have key : ∀ w ∈ T, QuaternionAlgebra.nrd (hatQ w x) ≠ 0 ∧
      ∃ q : ℍ[w.adicCompletion ℚ, cst w a, cst w b], IsInt (Ow w) q ∧
        cay (hatQ w x) - cay (ξ w) = (M₁ : w.adicCompletion ℚ) • q := by
    intro w hw
    obtain ⟨c₀, hc₀, e₀⟩ := hr₀ w hw
    obtain ⟨c₁, hc₁, e₁⟩ := hr₁ w hw
    obtain ⟨c₂, hc₂, e₂⟩ := hr₂ w hw
    obtain ⟨c₃, hc₃, e₃⟩ := hr₃ w hw

    obtain ⟨m, hm⟩ : pgen w ∣ P := Finset.dvd_prod_of_mem _ hw
    set r : ℍ[w.adicCompletion ℚ, cst w a, cst w b] := (m : w.adicCompletion ℚ) • ⟨c₀, c₁, c₂, c₃⟩ with hr
    have hrint : IsInt (Ow w) r := (show IsInt (Ow w) (⟨c₀, c₁, c₂, c₃⟩ : ℍ[w.adicCompletion ℚ, cst w a, cst w b])
      from ⟨hc₀, hc₁, hc₂, hc₃⟩).natCast_smul m
    have hxeq : hatQ w x = ξ w + ((M₁ : w.adicCompletion ℚ) * ((pgen w : ℕ) : w.adicCompletion ℚ) *
        (N₀ : w.adicCompletion ℚ) ^ 2 * (N₀ : w.adicCompletion ℚ) ^ 4 * (A : w.adicCompletion ℚ) ^ 4) • r := by
      rw [hr, smul_smul, hx, hatQ_mk]
      simp only [e₀, e₁, e₂, e₃]
      have hLK : (L : w.adicCompletion ℚ) = (M₁ : w.adicCompletion ℚ) * ((pgen w : ℕ) : w.adicCompletion ℚ) *
          (N₀ : w.adicCompletion ℚ) ^ 2 * (N₀ : w.adicCompletion ℚ) ^ 4 * (A : w.adicCompletion ℚ) ^ 4 * (m : w.adicCompletion ℚ) := by
        rw [hL, hm]; push_cast; ring
      obtain ⟨ξ₀, ξ₁, ξ₂, ξ₃⟩ := ξ w
      ext <;> simp [hLK]
    rw [hxeq]
    exact cay_estimate (𝒪 := Ow w) (hA w).1 (hA w).2 _ (natCast_mem _ _) (hunit_pgen w) N₀ N₀
      (natCast_adicCompletion_ne_zero w hN₀) (ξ w) (hN w hw).1 (hξ w hw) (hN w hw).2
      (M₁ : w.adicCompletion ℚ) (natCast_mem _ _) r hrint
  obtain ⟨w₀, hw₀⟩ := hT
  refine ⟨x, ?_, fun w hw => (key w hw).2⟩
  intro h0
  apply (key w₀ hw₀).1
  rw [nrd_hatQ, h0]
  exact map_zero (algebraMap ℚ (w₀.adicCompletion ℚ))

end Core

end WACC
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset.WACC"

namespace WACC

open IsDedekindDomain NumberField
open scoped TensorProduct

section Final

variable {a b : ℚ}

def IsCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) : Prop :=
  ∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
    φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])

theorem exists_isCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      IsCoord a b w φ := by
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (w.adicCompletion ℚ) a) (d₂ := (0 : w.adicCompletion ℚ))
    (d₃ := algebraMap ℚ (w.adicCompletion ℚ) b) rfl (map_zero _) rfl AlgEquiv.refl
  exact ⟨φ, fun z r => by rw [hφ]; rfl⟩

variable {w : HeightOneSpectrum (𝓞 ℚ)}
  {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
    ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}

theorem IsCoord.tmul (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ) :
    φ (z ⊗ₜ[ℚ] r) = r • hatQ w z := by
  rw [hφ]; rfl

theorem IsCoord.tmul_one (hφ : IsCoord a b w φ) (z : ℍ[ℚ, a, b]) :
    φ (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = hatQ w z := by
  rw [hφ.tmul, one_smul]

theorem IsCoord.natCast_smul (hφ : IsCoord a b w φ) (M : ℕ) (y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    φ ((M : ℚ) • y) = (M : w.adicCompletion ℚ) • φ y := by
  have h0 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((M : w.adicCompletion ℚ)))
      = (M : ℚ) • (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def,
      mul_one, map_natCast]
  have h1 : (M : ℚ) • y = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((M : w.adicCompletion ℚ))) * y := by
    rw [h0, smul_mul_assoc, one_mul]
  rw [h1, RingEquiv.map_mul, hφ.tmul, hatQ_one, smul_mul_assoc, one_mul]

theorem exists_natCast_smul_mem_of_mem_span (Λ : Submodule ℤ ℍ[ℚ, a, b]) {y : ℍ[ℚ, a, b]}
    (hy : y ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b])) : ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • y ∈ Λ := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_ne_zero, by simpa using hz⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨m, hm, hmu⟩ := hu
    obtain ⟨n, hn, hnv⟩ := hv
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul ℚ n]
      exact Λ.smul_of_tower_mem n hmu
    · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul ℚ m]
      exact Λ.smul_of_tower_mem m hnv
  | smul c u _ hu =>
    obtain ⟨n, hn, hnu⟩ := hu
    refine ⟨c.den * n, mul_ne_zero c.den_ne_zero hn, ?_⟩
    have : ((c.den * n : ℕ) : ℚ) • c • u = (c.num : ℚ) • ((n : ℚ) • u) := by
      rw [smul_smul, smul_smul]
      congr 1
      push_cast
      have := Rat.den_mul_eq_num c
      linear_combination (n : ℚ) * this
    rw [this, Int.cast_smul_eq_zsmul ℚ]
    exact Λ.smul_mem _ hnu

theorem natCast_smul_mem_of_dvd (Λ : Submodule ℤ ℍ[ℚ, a, b]) {y : ℍ[ℚ, a, b]} {n m : ℕ}
    (h : (n : ℚ) • y ∈ Λ) (hnm : n ∣ m) : (m : ℚ) • y ∈ Λ := by
  obtain ⟨k, rfl⟩ := hnm
  rw [Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul ℚ k]
  exact Λ.smul_of_tower_mem k h

theorem exists_basis_mul_mem {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : ℚ) • (⟨1, 0, 0, 0⟩ : ℍ[ℚ, a, b]) ∈ O ∧ (N : ℚ) • (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) ∈ O ∧
      (N : ℚ) • (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) ∈ O ∧ (N : ℚ) • (⟨0, 0, 0, 1⟩ : ℍ[ℚ, a, b]) ∈ O := by
  have hsp : ∀ y : ℍ[ℚ, a, b], y ∈ Submodule.span ℚ (O : Set ℍ[ℚ, a, b]) := fun y => by
    rw [hO.spanTop]; exact Submodule.mem_top
  obtain ⟨n₀, h₀, m₀⟩ := exists_natCast_smul_mem_of_mem_span O (hsp ⟨1, 0, 0, 0⟩)
  obtain ⟨n₁, h₁, m₁⟩ := exists_natCast_smul_mem_of_mem_span O (hsp ⟨0, 1, 0, 0⟩)
  obtain ⟨n₂, h₂, m₂⟩ := exists_natCast_smul_mem_of_mem_span O (hsp ⟨0, 0, 1, 0⟩)
  obtain ⟨n₃, h₃, m₃⟩ := exists_natCast_smul_mem_of_mem_span O (hsp ⟨0, 0, 0, 1⟩)
  refine ⟨n₀ * n₁ * n₂ * n₃, ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero h₀ h₁) h₂) h₃
  · exact natCast_smul_mem_of_dvd O m₀ ⟨n₁ * n₂ * n₃, by ring⟩
  · exact natCast_smul_mem_of_dvd O m₁ ⟨n₀ * n₂ * n₃, by ring⟩
  · exact natCast_smul_mem_of_dvd O m₂ ⟨n₀ * n₁ * n₃, by ring⟩
  · exact natCast_smul_mem_of_dvd O m₃ ⟨n₀ * n₁ * n₂, by ring⟩

theorem exists_mem_localBox_map_eq (hφ : IsCoord a b w φ) {O : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (h1 : (N : ℚ) • (⟨1, 0, 0, 0⟩ : ℍ[ℚ, a, b]) ∈ O) (hi : (N : ℚ) • (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) ∈ O)
    (hj : (N : ℚ) • (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) ∈ O) (hk : (N : ℚ) • (⟨0, 0, 0, 1⟩ : ℍ[ℚ, a, b]) ∈ O)
    (Q : ℍ[w.adicCompletion ℚ, cst w a, cst w b]) (hQ : IsInt (Ow w) Q) :
    ∃ z ∈ Submodule.localBox O w, φ z = (N : w.adicCompletion ℚ) • Q := by
  refine ⟨((N : ℚ) • (⟨1, 0, 0, 0⟩ : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] Q.re + ((N : ℚ) • (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] Q.imI
    + ((N : ℚ) • (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] Q.imJ + ((N : ℚ) • (⟨0, 0, 0, 1⟩ : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] Q.imK,
    ?_, ?_⟩
  · have gen : ∀ {y : ℍ[ℚ, a, b]} (hy : y ∈ O) {c : w.adicCompletion ℚ} (hc : c ∈ Ow w),
        y ⊗ₜ[ℚ] c ∈ Submodule.localBox O w := fun {y} hy {c} hc =>
      AddSubgroup.subset_closure ⟨y, hy, c, hc, rfl⟩
    exact AddSubgroup.add_mem _ (AddSubgroup.add_mem _ (AddSubgroup.add_mem _ (gen h1 hQ.1) (gen hi hQ.2.1))
      (gen hj hQ.2.2.1)) (gen hk hQ.2.2.2)
  · simp only [RingEquiv.map_add, hφ.tmul, hatQ_smul, hatQ_mk]
    obtain ⟨Q₀, Q₁, Q₂, Q₃⟩ := Q
    ext <;> simp [cst] <;> ring

theorem prod_pos {K : Type*} [Field K] {𝒪 : Subring K} {c₁ c₃ : K} {A : ℕ}
    (hA : (A : K) * c₁ ∈ 𝒪) (hB : (A : K) * c₃ ∈ 𝒪) (M N N₁ : ℕ)
    (σ q q' : ℍ[K, c₁, c₃]) (hσ : IsInt 𝒪 ((N₁ : K) • σ)) (hq : IsInt 𝒪 q) (hq' : IsInt 𝒪 q') :
    ∃ Q : ℍ[K, c₁, c₃], IsInt 𝒪 Q ∧
      -((σ + ((M * N * N₁ * A ^ 2 : ℕ) : K) • q) * (-1 + ((M * N * N₁ * A ^ 2 : ℕ) : K) • q'))
        = σ + ((M * N : ℕ) : K) • Q := by
  refine ⟨((N₁ * A ^ 2 : ℕ) : K) • q - ((A : K) ^ 2) • (((N₁ : K) • σ) * q')
      - ((N₁ * (M * N * N₁ * A ^ 2) : ℕ) : K) • (((A : K) ^ 2) • (q * q')), ?_, ?_⟩
  · exact ((hq.natCast_smul _).sub (hσ.mul hA hB hq')).sub ((hq.mul hA hB hq').natCast_smul _)
  · push_cast
    simp only [mul_add, add_mul, mul_neg, neg_mul, mul_one, one_mul, neg_neg, smul_mul_assoc, mul_smul_comm,
      smul_sub, smul_add, smul_neg, smul_smul, neg_add_rev]
    module

theorem prod_neg {K : Type*} [Field K] {𝒪 : Subring K} {c₁ c₃ : K} {A : ℕ}
    (hA : (A : K) * c₁ ∈ 𝒪) (hB : (A : K) * c₃ ∈ 𝒪) (M N N₁ : ℕ)
    (σ q q' : ℍ[K, c₁, c₃]) (hσ : IsInt 𝒪 ((N₁ : K) • σ)) (hq : IsInt 𝒪 q) (hq' : IsInt 𝒪 q') :
    ∃ Q : ℍ[K, c₁, c₃], IsInt 𝒪 Q ∧
      -((1 + ((M * N * N₁ * A ^ 2 : ℕ) : K) • q) * (-σ + ((M * N * N₁ * A ^ 2 : ℕ) : K) • q'))
        = σ + ((M * N : ℕ) : K) • Q := by
  refine ⟨-(((N₁ * A ^ 2 : ℕ) : K) • q') + ((A : K) ^ 2) • (q * ((N₁ : K) • σ))
      - ((N₁ * (M * N * N₁ * A ^ 2) : ℕ) : K) • (((A : K) ^ 2) • (q * q')), ?_, ?_⟩
  · exact (((hq'.natCast_smul _).neg).add (hq.mul hA hB hσ)).sub ((hq.mul hA hB hq').natCast_smul _)
  · push_cast
    simp only [mul_add, add_mul, mul_neg, neg_mul, mul_one, one_mul, neg_neg, smul_mul_assoc, mul_smul_comm,
      smul_sub, smul_add, smul_neg, smul_smul, neg_add_rev]
    module

theorem four_ne_zero' (w : HeightOneSpectrum (𝓞 ℚ)) : (4 : w.adicCompletion ℚ) ≠ 0 := by
  have := natCast_adicCompletion_ne_zero w (n := 4) (by norm_num)
  exact_mod_cast this

theorem main (ha : a ≠ 0) (hb : b ≠ 0)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (s : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)
    (hs : ∀ w ∈ T, ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      IsCoord a b w φ → QuaternionAlgebra.nrd (φ (s w)) = 1)
    (M : ℕ) (hM : M ≠ 0) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = 1 ∧
      ∀ w ∈ T, ∃ z ∈ Submodule.localBox O w,
        γ ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = s w + (M : ℚ) • z := by
  classical
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨1, QuaternionAlgebra.nrd_one, by simp [hT]⟩

  choose φ hφ using fun w => exists_isCoord a b w
  set σ : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[w.adicCompletion ℚ, cst w a, cst w b] := fun w => φ w (s w) with hσ
  have hσ1 : ∀ w ∈ T, QuaternionAlgebra.nrd (σ w) = 1 := fun w hw => hs w hw (φ w) (hφ w)

  obtain ⟨A, hA0, hA⟩ := exists_den a b
  obtain ⟨N, hN0, hN1, hNi, hNj, hNk⟩ := exists_basis_mul_mem hO
  obtain ⟨N₁, hN₁0, hN₁⟩ := exists_nat_clear T σ
  set M₁ : ℕ := M * N * N₁ * A ^ 2 with hM₁
  have hM₁0 : M₁ ≠ 0 := by
    rw [hM₁]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hM hN0) hN₁0) (pow_ne_zero _ hA0)

  have hsum : ∀ w ∈ T, QuaternionAlgebra.nrd (1 + σ w) + QuaternionAlgebra.nrd (1 - σ w) = 4 := by
    intro w hw
    rw [nrd_one_add, nrd_one_sub, hσ1 w hw]; ring

  set ξp : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[w.adicCompletion ℚ, cst w a, cst w b] :=
    fun w => if QuaternionAlgebra.nrd (1 + σ w) ≠ 0 then 1 + σ w else 1 + 1 with hξp
  set ξm : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[w.adicCompletion ℚ, cst w a, cst w b] :=
    fun w => if QuaternionAlgebra.nrd (1 + σ w) ≠ 0 then ⟨0, 1, 0, 0⟩ else 1 - σ w with hξm
  have h11 : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      QuaternionAlgebra.nrd ((1 : ℍ[w.adicCompletion ℚ, cst w a, cst w b]) + 1) ≠ 0 := by
    intro w
    rw [nrd_one_add, QuaternionAlgebra.nrd_one, trd_eq]
    simp only [QuaternionAlgebra.re_one]
    norm_num
    exact four_ne_zero' w
  have hcsta : ∀ w : HeightOneSpectrum (𝓞 ℚ), cst w a ≠ 0 := fun w =>
    (map_ne_zero_iff _ (algebraMap ℚ (w.adicCompletion ℚ)).injective).2 ha
  have hnrdi : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      QuaternionAlgebra.nrd (⟨0, 1, 0, 0⟩ : ℍ[w.adicCompletion ℚ, cst w a, cst w b]) ≠ 0 := by
    intro w
    rw [QuaternionAlgebra.nrd_mk,
      show (0 : w.adicCompletion ℚ) ^ 2 - cst w a * 1 ^ 2 - cst w b * 0 ^ 2 + cst w a * cst w b * 0 ^ 2 = -cst w a by ring]
    exact neg_ne_zero.2 (hcsta w)
  have hξp_pos : ∀ w, QuaternionAlgebra.nrd (1 + σ w) ≠ 0 → ξp w = 1 + σ w := by
    intro w hc; rw [hξp]; exact if_pos hc
  have hξp_neg : ∀ w, ¬ (QuaternionAlgebra.nrd (1 + σ w) ≠ 0) → ξp w = 1 + 1 := by
    intro w hc; rw [hξp]; exact if_neg hc
  have hξm_pos : ∀ w, QuaternionAlgebra.nrd (1 + σ w) ≠ 0 → ξm w = ⟨0, 1, 0, 0⟩ := by
    intro w hc; rw [hξm]; exact if_pos hc
  have hξm_neg : ∀ w, ¬ (QuaternionAlgebra.nrd (1 + σ w) ≠ 0) → ξm w = 1 - σ w := by
    intro w hc; rw [hξm]; exact if_neg hc
  have hminus : ∀ w ∈ T, ¬ (QuaternionAlgebra.nrd (1 + σ w) ≠ 0) → QuaternionAlgebra.nrd (1 - σ w) ≠ 0 := by
    intro w hw hc
    push Not at hc
    have := hsum w hw
    rw [hc, zero_add] at this
    rw [this]; exact four_ne_zero' w
  have hξp0 : ∀ w ∈ T, QuaternionAlgebra.nrd (ξp w) ≠ 0 := by
    intro w hw
    by_cases hc : QuaternionAlgebra.nrd (1 + σ w) ≠ 0
    · rw [hξp_pos w hc]; exact hc
    · rw [hξp_neg w hc]; exact h11 w
  have hξm0 : ∀ w ∈ T, QuaternionAlgebra.nrd (ξm w) ≠ 0 := by
    intro w hw
    by_cases hc : QuaternionAlgebra.nrd (1 + σ w) ≠ 0
    · rw [hξm_pos w hc]; exact hnrdi w
    · rw [hξm_neg w hc]; exact hminus w hw hc

  obtain ⟨xp, hxp0, hxp⟩ := core_approx T hT ξp hξp0 M₁ hM₁0
  obtain ⟨xm, hxm0, hxm⟩ := core_approx T hT ξm hξm0 M₁ hM₁0
  refine ⟨-(cayQ xp * cayQ xm), ?_, fun w hw => ?_⟩
  · rw [QuaternionAlgebra.nrd_neg, nrd_mul', nrd_cayQ hxp0, nrd_cayQ hxm0, one_mul]

  obtain ⟨q, hq, eq⟩ := hxp w hw
  obtain ⟨q', hq', eq'⟩ := hxm w hw
  have hcp : cay (hatQ w xp) = cay (ξp w) + (M₁ : w.adicCompletion ℚ) • q := by rw [← eq]; abel
  have hcm : cay (hatQ w xm) = cay (ξm w) + (M₁ : w.adicCompletion ℚ) • q' := by rw [← eq']; abel
  have hγ : hatQ w (-(cayQ xp * cayQ xm))
      = -((cay (ξp w) + (M₁ : w.adicCompletion ℚ) • q) * (cay (ξm w) + (M₁ : w.adicCompletion ℚ) • q')) := by
    rw [hatQ_neg, hatQ_mul, hatQ_cayQ, hatQ_cayQ, hcp, hcm]

  obtain ⟨Q, hQ, hγQ⟩ : ∃ Q : ℍ[w.adicCompletion ℚ, cst w a, cst w b], IsInt (Ow w) Q ∧
      hatQ w (-(cayQ xp * cayQ xm)) = σ w + ((M * N : ℕ) : w.adicCompletion ℚ) • Q := by
    rw [hγ]
    by_cases hc : QuaternionAlgebra.nrd (1 + σ w) ≠ 0
    · have e1 : cay (ξp w) = σ w := by
        rw [hξp_pos w hc]; exact cay_one_add (hσ1 w hw) hc
      have e2 : cay (ξm w) = -1 := by
        rw [hξm_pos w hc]; exact cay_i (hcsta w)
      rw [e1, e2, hM₁]
      exact prod_pos (hA w).1 (hA w).2 M N N₁ (σ w) q q' (hN₁ w hw).1 hq hq'
    · have e1 : cay (ξp w) = 1 := by
        rw [hξp_neg w hc]; exact cay_one_add QuaternionAlgebra.nrd_one (h11 w)
      have e2 : cay (ξm w) = -σ w := by
        rw [hξm_neg w hc]; exact cay_one_sub (hσ1 w hw) (hminus w hw hc)
      rw [e1, e2, hM₁]
      exact prod_neg (hA w).1 (hA w).2 M N N₁ (σ w) q q' (hN₁ w hw).1 hq hq'

  obtain ⟨z, hz, hφz⟩ := exists_mem_localBox_map_eq (hφ w) hN1 hNi hNj hNk Q hQ
  refine ⟨z, hz, (φ w).injective ?_⟩
  rw [(hφ w).tmul_one, hγQ, RingEquiv.map_add, (hφ w).natCast_smul, hφz, smul_smul]
  push_cast
  rfl

end Final
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset.WACC"

end WACC
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset.WACC"

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem solution
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    {O : Submodule ℤ ℍ[ℚ, a, b]} (hO : QuaternionAlgebra.IsOrder O)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (s : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)
    (hs : ∀ w ∈ T,
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        (∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
          φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
            algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
            algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
              ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a,
                algebraMap ℚ (w.adicCompletion ℚ) b])) →
        QuaternionAlgebra.nrd (φ (s w)) = 1)
    (M : ℕ) (hM : M ≠ 0) :
    ∃ γ : ℍ[ℚ, a, b], QuaternionAlgebra.nrd γ = 1 ∧
      ∀ w ∈ T, ∃ z ∈ Submodule.localBox O w,
        γ ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) = s w + (M : ℚ) • z :=
  WACC.main ha hb hO T s hs M hM

end S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_forall_tmul_eq_add_smul_of_finset (solution)
