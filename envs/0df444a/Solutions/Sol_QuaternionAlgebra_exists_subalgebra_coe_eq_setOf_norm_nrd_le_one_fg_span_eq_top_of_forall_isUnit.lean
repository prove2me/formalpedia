-- Prove2me | solution 1 for QuaternionAlgebra.exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a8fe19ed-a107-5771-857e-6e1722071b12

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit

set_option autoImplicit false

open scoped Quaternion

namespace QuatVal

variable {p : ℕ} [Fact p.Prime] {a b : ℚ_[p]}

open QuaternionAlgebra

theorem nrd_mul (x y : ℍ[ℚ_[p], a, b]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]
  ring

theorem nrd_add (x y : ℍ[ℚ_[p], a, b]) : nrd (x + y) = nrd x + nrd y + trd (x * star y) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_add_mk, QuaternionAlgebra.star_mk, QuaternionAlgebra.mk_mul_mk, nrd_mk, trd_mk]
  ring

theorem nrd_smul (c : ℚ_[p]) (x : ℍ[ℚ_[p], a, b]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, nrd_mk, smul_eq_mul]
  ring

theorem nrd_ne_zero_of_isUnit {x : ℍ[ℚ_[p], a, b]} (hx : IsUnit x) : nrd x ≠ 0 := by
  obtain ⟨u, rfl⟩ := hx
  intro h0
  have h1 : nrd ((u : ℍ[ℚ_[p], a, b]) * (↑u⁻¹ : ℍ[ℚ_[p], a, b])) = 1 := by rw [Units.mul_inv, nrd_one]
  rw [nrd_mul, h0, zero_mul] at h1
  exact zero_ne_one h1

theorem norm_nrd_pow (z : ℍ[ℚ_[p], a, b]) (i : ℕ) : ‖nrd (z ^ i)‖ = ‖nrd z‖ ^ i := by
  induction i with
  | zero => rw [pow_zero, nrd_one, norm_one, pow_zero]
  | succ k ih => rw [pow_succ, nrd_mul, norm_mul, ih, pow_succ]

theorem norm_nrd_add_le_one (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x)
    {x y : ℍ[ℚ_[p], a, b]} (hx : ‖nrd x‖ ≤ 1) (hy : ‖nrd y‖ ≤ 1) : ‖nrd (x + y)‖ ≤ 1 := by
  have hxy : ‖nrd (x * star y)‖ ≤ 1 := by
    rw [nrd_mul, nrd_star, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  have htrd := QuaternionAlgebra.norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one p a b hdiv (x * star y) hxy
  rw [nrd_add]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hx hy)) htrd)

theorem norm_nrd_add_le_max (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x)
    (x y : ℍ[ℚ_[p], a, b]) : ‖nrd (x + y)‖ ≤ max ‖nrd x‖ ‖nrd y‖ := by

  wlog hle : ‖nrd x‖ ≤ ‖nrd y‖ generalizing x y
  · rw [add_comm, max_comm]; exact this y x (le_of_not_ge hle)
  rw [max_eq_right hle]
  by_cases hy0 : y = 0
  · subst hy0
    rw [nrd_zero, norm_zero] at hle
    have hx0 : ‖nrd x‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [add_zero, nrd_zero, norm_zero, hx0]
  obtain ⟨u, rfl⟩ := hdiv y hy0
  have hu0 : nrd (u : ℍ[ℚ_[p], a, b]) ≠ 0 := nrd_ne_zero_of_isUnit u.isUnit
  have hnu : ‖nrd (u : ℍ[ℚ_[p], a, b])‖ ≠ 0 := norm_ne_zero_iff.mpr hu0

  have hfac : x + (u : ℍ[ℚ_[p], a, b]) = (u : ℍ[ℚ_[p], a, b]) * ((↑u⁻¹ : ℍ[ℚ_[p], a, b]) * x + 1) := by
    rw [mul_add, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
  have h1 : ‖nrd ((↑u⁻¹ : ℍ[ℚ_[p], a, b]) * x)‖ ≤ 1 := by
    have hinv : nrd (↑u⁻¹ : ℍ[ℚ_[p], a, b]) * nrd (u : ℍ[ℚ_[p], a, b]) = 1 := by
      rw [← nrd_mul, Units.inv_mul, nrd_one]
    rw [nrd_mul, norm_mul]
    have : ‖nrd (↑u⁻¹ : ℍ[ℚ_[p], a, b])‖ = ‖nrd (u : ℍ[ℚ_[p], a, b])‖⁻¹ := by
      rw [← norm_inv]; congr 1; exact eq_inv_of_mul_eq_one_left hinv
    rw [this, inv_mul_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) hnu.symm), mul_one]
    exact hle
  have h2 := norm_nrd_add_le_one hdiv h1 (by rw [nrd_one, norm_one])
  rw [hfac, nrd_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) h2

theorem norm_nrd_le_one_of_isIntegral (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x)
    (z : ℍ[ℚ_[p], a, b]) (hz : IsIntegral ℤ_[p] z) : ‖nrd z‖ ≤ 1 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨f, hf, hfz⟩ := hz

  set n := f.natDegree with hn
  have hsum : z ^ n = -∑ i ∈ Finset.range n, (algebraMap ℤ_[p] ℍ[ℚ_[p], a, b] (f.coeff i)) * z ^ i := by
    have h := hfz
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, map_one, one_mul] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h

  have hval : ∀ i ∈ Finset.range n, ‖nrd ((algebraMap ℤ_[p] ℍ[ℚ_[p], a, b] (f.coeff i)) * z ^ i)‖ < ‖nrd z‖ ^ n := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [nrd_mul, norm_mul]
    have hc : ‖nrd (algebraMap ℤ_[p] ℍ[ℚ_[p], a, b] (f.coeff i))‖ ≤ 1 := by
      rw [show algebraMap ℤ_[p] ℍ[ℚ_[p], a, b] (f.coeff i) = ((f.coeff i : ℚ_[p]) : ℍ[ℚ_[p], a, b]) from rfl,
        nrd_coe, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one _)
    rw [norm_nrd_pow]
    calc ‖nrd ((algebraMap ℤ_[p] ℍ[ℚ_[p], a, b]) (f.coeff i))‖ * ‖nrd z‖ ^ i ≤ 1 * ‖nrd z‖ ^ i :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg _) _)
      _ = ‖nrd z‖ ^ i := one_mul _
      _ < ‖nrd z‖ ^ n := pow_lt_pow_right₀ hgt hi

  have hult : ∀ (s : Finset ℕ) (g : ℕ → ℍ[ℚ_[p], a, b]) (C : ℝ), 0 ≤ C → (∀ i ∈ s, ‖nrd (g i)‖ < C) → 0 < C →
      ‖nrd (∑ i ∈ s, g i)‖ < C := by
    intro s g C hC0 hg hCpos
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, nrd_zero, norm_zero]; exact hCpos
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      refine lt_of_le_of_lt (norm_nrd_add_le_max hdiv _ _) (max_lt (hg i (Finset.mem_insert_self i s)) ?_)
      exact ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))
  have hzn : ‖nrd (z ^ n)‖ = ‖nrd z‖ ^ n := norm_nrd_pow z n
  have hpos : 0 < ‖nrd z‖ ^ n := pow_pos (lt_trans zero_lt_one hgt) n
  have hlt := hult (Finset.range n) _ (‖nrd z‖ ^ n) hpos.le hval hpos
  rw [← nrd_neg, ← hsum, hzn] at hlt
  exact lt_irrefl _ hlt

end QuatVal

namespace QuatVal

variable {p : ℕ} [Fact p.Prime] {a b : ℚ_[p]}

open QuaternionAlgebra

theorem a_ne_zero_of_forall_isUnit (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) : a ≠ 0 := by
  intro ha
  let i : ℍ[ℚ_[p], a, b] := ⟨0, 1, 0, 0⟩
  have hi0 : i ≠ 0 := by intro h; have := congrArg QuaternionAlgebra.imI h; simp [i] at this
  have hii : i * i = 0 := by ext <;> simp [i, ha]
  obtain ⟨u, hu⟩ := hdiv i hi0
  apply hi0
  have : (↑u⁻¹ : ℍ[ℚ_[p], a, b]) * (i * i) = i := by rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
  rw [hii, mul_zero] at this
  exact this.symm

theorem b_ne_zero_of_forall_isUnit (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) : b ≠ 0 := by
  intro hb
  let j : ℍ[ℚ_[p], a, b] := ⟨0, 0, 1, 0⟩
  have hj0 : j ≠ 0 := by intro h; have := congrArg QuaternionAlgebra.imJ h; simp [j] at this
  have hjj : j * j = 0 := by ext <;> simp [j, hb]
  obtain ⟨u, hu⟩ := hdiv j hj0
  apply hj0
  have : (↑u⁻¹ : ℍ[ℚ_[p], a, b]) * (j * j) = j := by rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
  rw [hjj, mul_zero] at this
  exact this.symm

noncomputable def valRing (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) : Subalgebra ℤ_[p] ℍ[ℚ_[p], a, b] where
  carrier := {z | ‖nrd z‖ ≤ 1}
  mul_mem' := fun {x y} hx hy => by
    show ‖nrd (x * y)‖ ≤ 1
    rw [nrd_mul, norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by show ‖nrd (1 : ℍ[ℚ_[p], a, b])‖ ≤ 1; rw [nrd_one, norm_one]
  add_mem' := fun {x y} hx hy => norm_nrd_add_le_one hdiv hx hy
  zero_mem' := by show ‖nrd (0 : ℍ[ℚ_[p], a, b])‖ ≤ 1; rw [nrd_zero, norm_zero]; exact zero_le_one
  algebraMap_mem' := fun c => by
    show ‖nrd (algebraMap ℤ_[p] ℍ[ℚ_[p], a, b] c)‖ ≤ 1
    rw [show algebraMap ℤ_[p] ℍ[ℚ_[p], a, b] c = ((c : ℚ_[p]) : ℍ[ℚ_[p], a, b]) from rfl, nrd_coe, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one _)

theorem mem_valRing (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) (z : ℍ[ℚ_[p], a, b]) :
    z ∈ valRing hdiv ↔ ‖nrd z‖ ≤ 1 := Iff.rfl

theorem exists_pow_smul_mem_valRing (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) (z : ℍ[ℚ_[p], a, b]) :
    ∃ k : ℕ, ((p : ℚ_[p]) ^ k) • z ∈ valRing hdiv := by
  have hp : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < (‖nrd z‖ + 1)⁻¹ from by positivity) hp
  refine ⟨k, ?_⟩
  rw [mem_valRing, nrd_smul, norm_mul, norm_pow, norm_pow, ← pow_mul]
  have h1 : ‖(p : ℚ_[p])‖ ^ (k * 2) ≤ ‖(p : ℚ_[p])‖ ^ k :=
    pow_le_pow_of_le_one (norm_nonneg _) hp.le (Nat.le_mul_of_pos_right k two_pos)
  calc ‖(p : ℚ_[p])‖ ^ (k * 2) * ‖nrd z‖ ≤ ‖(p : ℚ_[p])‖ ^ k * ‖nrd z‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (‖nrd z‖ + 1)⁻¹ * ‖nrd z‖ := mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)
    _ ≤ 1 := by
        rw [inv_mul_le_iff₀ (by positivity)]; linarith [norm_nonneg (nrd z)]

theorem span_valRing_eq_top (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) :
    Submodule.span ℚ_[p] (valRing hdiv : Set ℍ[ℚ_[p], a, b]) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_valRing hdiv z
  have hpk : ((p : ℚ_[p]) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have : z = ((p : ℚ_[p]) ^ k)⁻¹ • (((p : ℚ_[p]) ^ k) • z) := by rw [smul_smul, inv_mul_cancel₀ hpk, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hk)

theorem trd_mul_smul_basis (z : ℍ[ℚ_[p], a, b]) (c : ℚ_[p]) :
    trd (z * (c • ⟨1, 0, 0, 0⟩)) = c * 2 * z.re ∧ trd (z * (c • ⟨0, 1, 0, 0⟩)) = c * (2 * a) * z.imI ∧
      trd (z * (c • ⟨0, 0, 1, 0⟩)) = c * (2 * b) * z.imJ ∧ trd (z * (c • ⟨0, 0, 0, 1⟩)) = -(c * (2 * a * b) * z.imK) := by
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  simp only [QuaternionAlgebra.smul_mk, smul_eq_mul, mul_zero, mul_one, QuaternionAlgebra.mk_mul_mk, trd_mk]
  refine ⟨by ring, by ring, by ring, by ring⟩

theorem fg_valRing (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) :
    (Subalgebra.toSubmodule (valRing hdiv)).FG := by
  have ha := a_ne_zero_of_forall_isUnit hdiv
  have hb := b_ne_zero_of_forall_isUnit hdiv
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  obtain ⟨k₀, hk₀⟩ := exists_pow_smul_mem_valRing hdiv (⟨1, 0, 0, 0⟩ : ℍ[ℚ_[p], a, b])
  obtain ⟨k₁, hk₁⟩ := exists_pow_smul_mem_valRing hdiv (⟨0, 1, 0, 0⟩ : ℍ[ℚ_[p], a, b])
  obtain ⟨k₂, hk₂⟩ := exists_pow_smul_mem_valRing hdiv (⟨0, 0, 1, 0⟩ : ℍ[ℚ_[p], a, b])
  obtain ⟨k₃, hk₃⟩ := exists_pow_smul_mem_valRing hdiv (⟨0, 0, 0, 1⟩ : ℍ[ℚ_[p], a, b])
  set d₀ : ℚ_[p] := (p : ℚ_[p]) ^ k₀ * 2 with hd₀
  set d₁ : ℚ_[p] := (p : ℚ_[p]) ^ k₁ * (2 * a) with hd₁
  set d₂ : ℚ_[p] := (p : ℚ_[p]) ^ k₂ * (2 * b) with hd₂
  set d₃ : ℚ_[p] := (p : ℚ_[p]) ^ k₃ * (2 * a * b) with hd₃
  have hp0 : ∀ k : ℕ, ((p : ℚ_[p]) ^ k) ≠ 0 := fun k => pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hd₀0 : d₀ ≠ 0 := mul_ne_zero (hp0 _) h2
  have hd₁0 : d₁ ≠ 0 := mul_ne_zero (hp0 _) (mul_ne_zero h2 ha)
  have hd₂0 : d₂ ≠ 0 := mul_ne_zero (hp0 _) (mul_ne_zero h2 hb)
  have hd₃0 : d₃ ≠ 0 := mul_ne_zero (hp0 _) (mul_ne_zero (mul_ne_zero h2 ha) hb)

  set e₀ : ℍ[ℚ_[p], a, b] := ⟨d₀⁻¹, 0, 0, 0⟩ with he₀
  set e₁ : ℍ[ℚ_[p], a, b] := ⟨0, d₁⁻¹, 0, 0⟩ with he₁
  set e₂ : ℍ[ℚ_[p], a, b] := ⟨0, 0, d₂⁻¹, 0⟩ with he₂
  set e₃ : ℍ[ℚ_[p], a, b] := ⟨0, 0, 0, d₃⁻¹⟩ with he₃
  set L : Submodule ℤ_[p] ℍ[ℚ_[p], a, b] := Submodule.span ℤ_[p] {e₀, e₁, e₂, e₃} with hL
  have hLfg : L.FG := Submodule.fg_span (Set.toFinite _)
  have hsub : Subalgebra.toSubmodule (valRing hdiv) ≤ L := by
    intro z hz
    change ‖nrd z‖ ≤ 1 at hz
    have htr : ∀ (w : ℍ[ℚ_[p], a, b]), w ∈ valRing hdiv → ‖trd (z * w)‖ ≤ 1 := by
      intro w hw
      apply QuaternionAlgebra.norm_trd_le_one_of_forall_isUnit_of_norm_nrd_le_one p a b hdiv
      rw [nrd_mul, norm_mul]; exact mul_le_one₀ hz (norm_nonneg _) hw
    obtain ⟨t0, t1, t2, t3⟩ := trd_mul_smul_basis z ((p : ℚ_[p]) ^ k₀)
    obtain ⟨-, t1, -, -⟩ := trd_mul_smul_basis z ((p : ℚ_[p]) ^ k₁)
    obtain ⟨-, -, t2, -⟩ := trd_mul_smul_basis z ((p : ℚ_[p]) ^ k₂)
    obtain ⟨-, -, -, t3⟩ := trd_mul_smul_basis z ((p : ℚ_[p]) ^ k₃)
    have i0 := htr _ hk₀; rw [t0, ← hd₀] at i0
    have i1 := htr _ hk₁; rw [t1, ← hd₁] at i1
    have i2 := htr _ hk₂; rw [t2, ← hd₂] at i2
    have i3 := htr _ hk₃; rw [t3, ← hd₃, norm_neg] at i3

    let c₀ : ℤ_[p] := ⟨d₀ * z.re, i0⟩
    let c₁ : ℤ_[p] := ⟨d₁ * z.imI, i1⟩
    let c₂ : ℤ_[p] := ⟨d₂ * z.imJ, i2⟩
    let c₃ : ℤ_[p] := ⟨d₃ * z.imK, i3⟩
    have hz_eq : z = (c₀ : ℚ_[p]) • e₀ + (c₁ : ℚ_[p]) • e₁ + (c₂ : ℚ_[p]) • e₂ + (c₃ : ℚ_[p]) • e₃ := by
      ext
      · simp [he₀, he₁, he₂, he₃, c₀]; field_simp
      · simp [he₀, he₁, he₂, he₃, c₁]; field_simp
      · simp [he₀, he₁, he₂, he₃, c₂]; field_simp
      · simp [he₀, he₁, he₂, he₃, c₃]; field_simp
    rw [hz_eq]
    have hm : ∀ (c : ℤ_[p]) (e : ℍ[ℚ_[p], a, b]), e ∈ ({e₀, e₁, e₂, e₃} : Set ℍ[ℚ_[p], a, b]) → (c : ℚ_[p]) • e ∈ L := by
      intro c e he
      have hce : (c : ℚ_[p]) • e = c • e := by exact IsScalarTower.algebraMap_smul ℤ_[p] c e
      rw [hce]
      exact Submodule.smul_mem _ _ (Submodule.subset_span he)
    refine add_mem (add_mem (add_mem (hm c₀ e₀ (by simp)) (hm c₁ e₁ (by simp))) (hm c₂ e₂ (by simp))) (hm c₃ e₃ (by simp))

  haveI : Module.Finite ℤ_[p] ↥L := Module.Finite.iff_fg.mpr hLfg
  haveI : IsNoetherian ℤ_[p] ↥L := isNoetherian_of_isNoetherianRing_of_finite ℤ_[p] ↥L
  have hfg' : (Submodule.comap L.subtype (Subalgebra.toSubmodule (valRing hdiv))).FG := IsNoetherian.noetherian _
  have h3 := hfg'.map L.subtype
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hsub] at h3
  exact h3

theorem exists_order (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) :
    ∃ O : Subalgebra ℤ_[p] ℍ[ℚ_[p], a, b],
      (O : Set ℍ[ℚ_[p], a, b]) = {z | ‖QuaternionAlgebra.nrd z‖ ≤ 1} ∧
      (Subalgebra.toSubmodule O).FG ∧
      Submodule.span ℚ_[p] (O : Set ℍ[ℚ_[p], a, b]) = ⊤ :=
  ⟨valRing hdiv, rfl, fg_valRing hdiv, span_valRing_eq_top hdiv⟩

end QuatVal

theorem solution
    (p : ℕ) [Fact p.Prime] (a b : ℚ_[p])
    (hdiv : ∀ x : ℍ[ℚ_[p], a, b], x ≠ 0 → IsUnit x) :
    ∃ O : Subalgebra ℤ_[p] ℍ[ℚ_[p], a, b],
      (O : Set ℍ[ℚ_[p], a, b]) = {z | ‖QuaternionAlgebra.nrd z‖ ≤ 1} ∧
      (Subalgebra.toSubmodule O).FG ∧
      Submodule.span ℚ_[p] (O : Set ℍ[ℚ_[p], a, b]) = ⊤ :=
  QuatVal.exists_order hdiv

end S_QuaternionAlgebra_exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit
end P2MW
export P2MW.S_QuaternionAlgebra_exists_subalgebra_coe_eq_setOf_norm_nrd_le_one_fg_span_eq_top_of_forall_isUnit (solution)
