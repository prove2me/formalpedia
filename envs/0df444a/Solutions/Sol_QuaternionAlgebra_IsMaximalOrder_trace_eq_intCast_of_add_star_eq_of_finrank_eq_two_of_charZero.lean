-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.trace_eq_intCast_of_add_star_eq_of_finrank_eq_two_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ae85b75a-becf-5988-bac9-4bc11cc78406

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_trace_eq_intCast_of_add_star_eq_of_finrank_eq_two_of_charZero

set_option autoImplicit false
open scoped Quaternion

namespace Ch0Body

open QuaternionAlgebra

theorem mul_self_eq_trace_smul_sub_det {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hV : Module.finrank k V = 2) (Φ : Module.End k V) :
    Φ * Φ = LinearMap.trace k V Φ • Φ - LinearMap.det Φ • (1 : Module.End k V) := by
  classical
  let bV := Module.finBasisOfFinrankEq k V hV
  apply (LinearMap.toMatrix bV bV).injective
  rw [LinearMap.toMatrix_mul, map_sub, map_smul, map_smul, LinearMap.toMatrix_one,
    LinearMap.trace_eq_matrix_trace k bV, ← LinearMap.det_toMatrix bV]
  set C := LinearMap.toMatrix bV bV Φ
  ext i j
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem a_ne_zero {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q') : a ≠ 0 := by
  intro ha
  have hu := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) (by
    intro h; have := congrArg QuaternionAlgebra.imI h; simp at this)
  have hn : nrd (⟨0, 1, 0, 0⟩ : ℍ[ℚ, a, b]) = 0 := by simp [nrd, ha]
  obtain ⟨u, hu'⟩ := hu
  have nm : ∀ x y : ℍ[ℚ, a, b], nrd (x * y) = nrd x * nrd y := by
    intro x y; obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
    simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring
  have h1 : nrd ((u : ℍ[ℚ, a, b]) * ((u⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1 := by rw [Units.mul_inv]; simp [nrd]
  rw [nm, hu', hn, zero_mul] at h1
  exact zero_ne_one h1

theorem b_ne_zero {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q') : b ≠ 0 := by
  intro hb
  have hu := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) (by
    intro h; have := congrArg QuaternionAlgebra.imJ h; simp at this)
  have hn : nrd (⟨0, 0, 1, 0⟩ : ℍ[ℚ, a, b]) = 0 := by simp [nrd, hb]
  obtain ⟨u, hu'⟩ := hu
  have nm : ∀ x y : ℍ[ℚ, a, b], nrd (x * y) = nrd x * nrd y := by
    intro x y; obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
    simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring
  have h1 : nrd ((u : ℍ[ℚ, a, b]) * ((u⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1 := by rw [Units.mul_inv]; simp [nrd]
  rw [nm, hu', hn, zero_mul] at h1
  exact zero_ne_one h1

end Ch0Body

open Ch0Body QuaternionAlgebra in
theorem solution
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {k : Type*} [Field k] [CharZero k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (hV : Module.finrank k V = 2)
    (θ : ↥Λ → Module.End k V)
    (hadd : ∀ x y : ↥Λ, θ (x + y) = θ x + θ y)
    (hone : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, θ ⟨1, h⟩ = 1)
    (hmul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      θ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = θ x * θ y)
    (m : ↥Λ) (n : ℤ) (hn : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) :
    LinearMap.trace k V (θ m) = (n : k) := by
  classical
  have hΛo : IsOrder Λ := hΛ.isOrder
  have ha0 := a_ne_zero hB
  have hb0 := b_ne_zero hB
  have hV0 : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by rw [hV]; norm_num)

  let θ' : ↥Λ →+ Module.End k V := AddMonoidHom.mk' θ hadd
  have hθ' : ∀ x, θ' x = θ x := fun x => rfl
  have θzsmul : ∀ (z : ℤ) (x : ↥Λ), θ (z • x) = z • θ x := fun z x => by rw [← hθ', map_zsmul, hθ']
  have θsub : ∀ x y : ↥Λ, θ (x - y) = θ x - θ y := fun x y => by rw [← hθ', map_sub, hθ', hθ']
  have h1Λ : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛo.one_mem
  have θneg : ∀ x : ↥Λ, θ (-x) = -θ x := fun x => by rw [← hθ', map_neg, hθ']
  have h10 : (1 : Module.End k V) ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h; apply hv; have := congrArg (fun T : Module.End k V => T v) h; simpa using this

  have θrat : ∀ (c : ℚ) (hc : ((c : ℚ) : ℍ[ℚ, a, b]) ∈ Λ), θ ⟨(c : ℍ[ℚ, a, b]), hc⟩ = (c : k) • (1 : Module.End k V) := by
    intro c hc
    have hnum : ((c.num : ℚ) : ℍ[ℚ, a, b]) = c.num • (1 : ℍ[ℚ, a, b]) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]
    have hden : (c.den : ℤ) • (⟨(c : ℍ[ℚ, a, b]), hc⟩ : ↥Λ) = c.num • (⟨1, h1Λ⟩ : ↥Λ) := by
      apply Subtype.ext
      simp only [SetLike.val_smul]
      rw [← hnum, ← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, ← coe_mul]
      congr 1; push_cast; exact Rat.den_mul_eq_num c
    have := congrArg θ hden
    rw [θzsmul, θzsmul, hone] at this

    have hdk : ((c.den : ℤ) : k) ≠ 0 := by exact_mod_cast c.den_ne_zero
    have e2 : ((c.den : ℤ) : k) • θ ⟨(c : ℍ[ℚ, a, b]), hc⟩ = ((c.num : ℤ) : k) • (1 : Module.End k V) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; exact this
    have := congrArg (fun T => (((c.den : ℤ) : k)⁻¹) • T) e2
    simp only [smul_smul, inv_mul_cancel₀ hdk, one_smul] at this
    rw [this, Rat.cast_def, div_eq_inv_mul]; norm_cast

  have lemA : ∀ (x y : ↥Λ) (c d : ℚ), c ≠ 0 → d ≠ 0 →
      (x : ℍ[ℚ, a, b]) * x = (c : ℍ[ℚ, a, b]) → (y : ℍ[ℚ, a, b]) * y = (d : ℍ[ℚ, a, b]) →
      (x : ℍ[ℚ, a, b]) * y = -((y : ℍ[ℚ, a, b]) * x) → LinearMap.trace k V (θ x) = 0 := by
    intro x y c d hc hd hxx hyy hxy
    have hcΛ : ((c : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hxx ▸ hΛo.mul_mem x.2 x.2
    have hdΛ : ((d : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := hyy ▸ hΛo.mul_mem y.2 y.2
    set Φ := θ x with hΦ
    set Ψ := θ y with hΨ
    have hΦ2 : Φ * Φ = (c : k) • 1 := by
      rw [hΦ, ← hmul x x (hΛo.mul_mem x.2 x.2)]
      rw [show (⟨(x : ℍ[ℚ, a, b]) * x, hΛo.mul_mem x.2 x.2⟩ : ↥Λ) = ⟨(c : ℍ[ℚ, a, b]), hcΛ⟩ from Subtype.ext hxx, θrat]
    have hΨ2 : Ψ * Ψ = (d : k) • 1 := by
      rw [hΨ, ← hmul y y (hΛo.mul_mem y.2 y.2)]
      rw [show (⟨(y : ℍ[ℚ, a, b]) * y, hΛo.mul_mem y.2 y.2⟩ : ↥Λ) = ⟨(d : ℍ[ℚ, a, b]), hdΛ⟩ from Subtype.ext hyy, θrat]
    have hΦΨ : Φ * Ψ = -(Ψ * Φ) := by
      rw [hΦ, hΨ, ← hmul x y (hΛo.mul_mem x.2 y.2), ← hmul y x (hΛo.mul_mem y.2 x.2), ← θneg]
      congr 1; apply Subtype.ext; simp [hxy]
    by_contra htr

    have hCH := mul_self_eq_trace_smul_sub_det hV Φ
    rw [hΦ2] at hCH
    have hΦsc : Φ = ((LinearMap.trace k V Φ)⁻¹ * ((c : k) + LinearMap.det Φ)) • (1 : Module.End k V) := by
      have : LinearMap.trace k V Φ • Φ = ((c : k) + LinearMap.det Φ) • (1 : Module.End k V) := by
        rw [add_smul, hCH]; abel
      have := congrArg (fun T => (LinearMap.trace k V Φ)⁻¹ • T) this
      simp only [smul_smul, inv_mul_cancel₀ htr, one_smul] at this
      exact this
    set lam := (LinearMap.trace k V Φ)⁻¹ * ((c : k) + LinearMap.det Φ) with hlam

    have h2 : ((2 : k) * lam) • Ψ = 0 := by
      have := hΦΨ
      rw [hΦsc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at this
      rw [mul_smul, two_smul]; exact add_eq_zero_iff_eq_neg.2 this
    rcases smul_eq_zero.1 h2 with h | h
    · rcases mul_eq_zero.1 h with h2' | hl
      · exact two_ne_zero h2'
      ·
        rw [hl, zero_smul] at hΦsc
        rw [hΦsc, mul_zero] at hΦ2
        rcases smul_eq_zero.1 hΦ2.symm with h' | h'
        · exact hc (by exact_mod_cast h')
        · exact h10 h'
    ·
      rw [h, mul_zero] at hΨ2
      rcases smul_eq_zero.1 hΨ2.symm with h' | h'
      · exact hd (by exact_mod_cast h')
      · exact h10 h'

  let qi : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩
  let qj : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩
  let qk : ℍ[ℚ, a, b] := ⟨0, 0, 0, 1⟩
  have hspan : ∀ y : ℍ[ℚ, a, b], y ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) := fun y => by
    rw [hΛo.spanTop]; exact Submodule.mem_top
  obtain ⟨N, hN0, hN⟩ := exists_natCast_smul_mem_of_mem_span (hspan (qi + qj))

  obtain ⟨Ni, hNi0, hNi⟩ := exists_natCast_smul_mem_of_mem_span (hspan qi)
  obtain ⟨Nj, hNj0, hNj⟩ := exists_natCast_smul_mem_of_mem_span (hspan qj)

  have sq_smul : ∀ (r : ℚ) (e : ℍ[ℚ, a, b]) (c : ℚ), e * e = (c : ℍ[ℚ, a, b]) →
      (r • e) * (r • e) = ((r * r * c : ℚ) : ℍ[ℚ, a, b]) := by
    intro r e c he
    rw [smul_mul_assoc, mul_smul_comm, he, smul_smul, ← coe_mul_eq_smul]; push_cast; ring
  have hqi : qi * qi = (a : ℍ[ℚ, a, b]) := by ext <;> simp [qi]
  have hqj : qj * qj = (b : ℍ[ℚ, a, b]) := by ext <;> simp [qj]
  have hqk : qk * qk = ((-(a * b) : ℚ) : ℍ[ℚ, a, b]) := by ext <;> simp [qk]
  have hij : ∀ r s : ℚ, (r • qi) * (s • qj) = -((s • qj) * (r • qi)) := by intro r s; ext <;> simp [qi, qj] <;> ring
  have hji : ∀ r s : ℚ, (r • qj) * (s • qi) = -((s • qi) * (r • qj)) := by intro r s; ext <;> simp [qi, qj] <;> ring
  have hki : ∀ r s : ℚ, (r • qk) * (s • qi) = -((s • qi) * (r • qk)) := by intro r s; ext <;> simp [qi, qk] <;> ring
  have natsmul_eq : ∀ (M : ℕ) (y : ℍ[ℚ, a, b]), ((M : ℕ) : ℤ) • y = (M : ℚ) • y := fun M y => by
    rw [← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl
  have trz : ∀ (r : ℚ) (e e' : ℍ[ℚ, a, b]) (c c' : ℚ) (M : ℕ), M ≠ 0 → c ≠ 0 → c' ≠ 0 →
      e * e = (c : ℍ[ℚ, a, b]) → e' * e' = (c' : ℍ[ℚ, a, b]) →
      (∀ r s : ℚ, (r • e) * (s • e') = -((s • e') * (r • e))) →
      ∀ (hx : r • e ∈ Λ) (hy : ((M : ℕ) : ℤ) • e' ∈ Λ), LinearMap.trace k V (θ ⟨r • e, hx⟩) = 0 := by
    intro r e e' c c' M hM hc hc' he he' hanti hx hy
    by_cases hr : r = 0
    · have : (⟨r • e, hx⟩ : ↥Λ) = 0 := Subtype.ext (by simp [hr])
      rw [this, ← hθ', map_zero, map_zero]
    · have hy' : (M : ℚ) • e' ∈ Λ := by rw [← natsmul_eq]; exact hy
      refine lemA ⟨r • e, hx⟩ ⟨(M : ℚ) • e', hy'⟩ (r * r * c) ((M : ℚ) * M * c')
        (mul_ne_zero (mul_ne_zero hr hr) hc)
        (mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 hM) (Nat.cast_ne_zero.2 hM)) hc')
        (sq_smul r e c he) (sq_smul _ e' c' he') (hanti r _)

  have hnΛ : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [show ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) by
      rw [← Int.cast_smul_eq_zsmul ℚ, ← coe_mul_eq_smul, mul_one]]
    exact Λ.smul_mem _ h1Λ
  have hstarΛ : star (m : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [show star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) - m from by rw [← hn]; abel]
    exact sub_mem hnΛ m.2
  set m₁ := (m : ℍ[ℚ, a, b]).imI
  set m₂ := (m : ℍ[ℚ, a, b]).imJ
  set m₃ := (m : ℍ[ℚ, a, b]).imK
  have hz : (m : ℍ[ℚ, a, b]) - star (m : ℍ[ℚ, a, b]) = (2 * m₁) • qi + (2 * m₂) • qj + (2 * m₃) • qk := by
    ext <;> simp [qi, qj, qk, m₁, m₂, m₃, QuaternionAlgebra.star_mk] <;> ring

  obtain ⟨d₁, hd₁0, hd₁⟩ := exists_natCast_smul_mem_of_mem_span (hspan ((2 * m₁) • qi))
  obtain ⟨d₂, hd₂0, hd₂⟩ := exists_natCast_smul_mem_of_mem_span (hspan ((2 * m₂) • qj))
  obtain ⟨d₃, hd₃0, hd₃⟩ := exists_natCast_smul_mem_of_mem_span (hspan ((2 * m₃) • qk))
  let D : ℕ := d₁ * d₂ * d₃
  have hD0 : D ≠ 0 := mul_ne_zero (mul_ne_zero hd₁0 hd₂0) hd₃0
  have hw₁ : ((D : ℚ) * (2 * m₁)) • qi ∈ Λ := by
    have : ((D : ℚ) * (2 * m₁)) • qi = (((d₂ * d₃ : ℕ) : ℤ)) • ((((d₁ : ℕ) : ℤ)) • ((2 * m₁) • qi)) := by
      rw [natsmul_eq, natsmul_eq, smul_smul, smul_smul]; congr 1 <;> simp only [D, Nat.cast_mul] <;> ring
    rw [this]; exact Λ.smul_mem _ hd₁
  have hw₂ : ((D : ℚ) * (2 * m₂)) • qj ∈ Λ := by
    have : ((D : ℚ) * (2 * m₂)) • qj = (((d₁ * d₃ : ℕ) : ℤ)) • ((((d₂ : ℕ) : ℤ)) • ((2 * m₂) • qj)) := by
      rw [natsmul_eq, natsmul_eq, smul_smul, smul_smul]; congr 1 <;> simp only [D, Nat.cast_mul] <;> ring
    rw [this]; exact Λ.smul_mem _ hd₂
  have hw₃ : ((D : ℚ) * (2 * m₃)) • qk ∈ Λ := by
    have : ((D : ℚ) * (2 * m₃)) • qk = (((d₁ * d₂ : ℕ) : ℤ)) • ((((d₃ : ℕ) : ℤ)) • ((2 * m₃) • qk)) := by
      rw [natsmul_eq, natsmul_eq, smul_smul, smul_smul]; congr 1 <;> simp only [D, Nat.cast_mul] <;> ring
    rw [this]; exact Λ.smul_mem _ hd₃

  have t₁ := trz ((D : ℚ) * (2 * m₁)) qi qj a b Nj hNj0 ha0 hb0 hqi hqj hij hw₁ hNj
  have t₂ := trz ((D : ℚ) * (2 * m₂)) qj qi b a Ni hNi0 hb0 ha0 hqj hqi hji hw₂ hNi
  have t₃ := trz ((D : ℚ) * (2 * m₃)) qk qi (-(a * b)) a Ni hNi0 (neg_ne_zero.2 (mul_ne_zero ha0 hb0)) ha0 hqk hqi hki hw₃ hNi

  let zΛ : ↥Λ := m - ⟨star (m : ℍ[ℚ, a, b]), hstarΛ⟩
  have hDz : ((D : ℕ) : ℤ) • zΛ = ⟨_, hw₁⟩ + ⟨_, hw₂⟩ + ⟨_, hw₃⟩ := by
    apply Subtype.ext
    simp only [SetLike.val_smul, Submodule.coe_add, Submodule.coe_sub, zΛ]
    rw [hz, natsmul_eq, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
  have htrz : LinearMap.trace k V (θ zΛ) = 0 := by
    have := congrArg (fun x => LinearMap.trace k V (θ x)) hDz
    simp only [θzsmul, hadd, map_add, map_zsmul, t₁, t₂, t₃, add_zero] at this
    have hDk : ((D : ℕ) : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hD0
    exact (smul_eq_zero.1 this).elim (fun h => absurd h hDk) id

  have hθstar : θ ⟨star (m : ℍ[ℚ, a, b]), hstarΛ⟩ = (n : k) • (1 : Module.End k V) - θ m := by
    have e : (⟨star (m : ℍ[ℚ, a, b]), hstarΛ⟩ : ↥Λ) = ⟨((n : ℚ) : ℍ[ℚ, a, b]), hnΛ⟩ - m :=
      Subtype.ext (by simp only [Submodule.coe_sub]; rw [← hn]; abel)
    rw [e, θsub, θrat, Rat.cast_intCast]
  rw [show θ zΛ = θ m - θ ⟨star (m : ℍ[ℚ, a, b]), hstarΛ⟩ from θsub _ _, hθstar, map_sub, map_sub, map_smul,
    LinearMap.trace_one, hV] at htrz
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  have : (2 : k) * (LinearMap.trace k V (θ m) - (n : k)) = 0 := by
    simp only [smul_eq_mul, Nat.cast_ofNat] at htrz
    linear_combination htrz
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h h2
  · exact sub_eq_zero.1 h

end S_QuaternionAlgebra_IsMaximalOrder_trace_eq_intCast_of_add_star_eq_of_finrank_eq_two_of_charZero
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_trace_eq_intCast_of_add_star_eq_of_finrank_eq_two_of_charZero (solution)
