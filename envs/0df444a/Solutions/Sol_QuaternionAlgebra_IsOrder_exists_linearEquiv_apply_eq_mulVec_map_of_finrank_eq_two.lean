-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/899ccfd8-d7f5-5e4d-a668-b7f02d20bf33

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two

set_option autoImplicit false

open scoped Quaternion
open QuaternionAlgebra CerednikDrinfeld

noncomputable section

namespace StdCoord

variable {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]

omit [Fact q'.Prime] in

theorem ne_zero_and_ne_zero (hB : IsIndefiniteRamifiedExactlyAt a b q q') : a ≠ 0 ∧ b ≠ 0 := by
  have key : ∀ y : ℍ[ℚ, a, b], y ≠ 0 → y * y = 0 → False := by
    intro y hy hyy
    obtain ⟨u, rfl⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB y hy
    apply hy
    calc (u : ℍ[ℚ, a, b]) = ↑u⁻¹ * (↑u * ↑u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = 0 := by rw [hyy, mul_zero]
  refine ⟨fun h0 => key ⟨0, 1, 0, 0⟩ ?_ ?_, fun h0 => key ⟨0, 0, 1, 0⟩ ?_ ?_⟩
  · intro h; simpa using congrArg QuaternionAlgebra.imI h
  · ext <;> simp [h0]
  · intro h; simpa using congrArg QuaternionAlgebra.imJ h
  · ext <;> simp [h0]

abbrev cx (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℂ := A.map (algebraMap ℝ ℂ)

theorem cx_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) : cx (A * B) = cx A * cx B := Matrix.map_mul
theorem cx_one : cx (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  simp [cx]
theorem cx_add (A B : Matrix (Fin 2) (Fin 2) ℝ) : cx (A + B) = cx A + cx B := by ext i j; simp [cx]
theorem cx_neg (A : Matrix (Fin 2) (Fin 2) ℝ) : cx (-A) = -cx A := by ext i j; simp [cx]
theorem cx_smul (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) : cx (r • A) = (r : ℂ) • cx A := by
  ext i j; simp [cx, Matrix.map_apply]

theorem exists_nsmul_mem_of_mem_span {W : Type*} [AddCommGroup W] [Module ℚ W]
    (M : Submodule ℤ W) {y : W} (hy : y ∈ Submodule.span ℚ (M : Set W)) :
    ∃ n : ℕ, 0 < n ∧ ((n : ℚ) • y) ∈ M := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hxm⟩ := hx
    obtain ⟨n, hn, hyn⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [smul_add]
    have h1 : ((m * n : ℕ) : ℚ) • x = (n : ℤ) • (((m : ℕ) : ℚ) • x) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]; push_cast; ring
    have h2 : ((m * n : ℕ) : ℚ) • y = (m : ℤ) • (((n : ℕ) : ℚ) • y) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul]; push_cast; ring
    rw [h1, h2]
    exact M.add_mem (M.smul_mem _ hxm) (M.smul_mem _ hyn)
  | smul r x _ hx =>
    obtain ⟨n, hn, hxn⟩ := hx
    refine ⟨n * r.den, Nat.mul_pos hn r.den_pos, ?_⟩
    have h1 : ((n * r.den : ℕ) : ℚ) • (r • x) = (r.num : ℤ) • (((n : ℕ) : ℚ) • x) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul, ← Rat.den_mul_eq_num r]
      push_cast; ring_nf
    rw [h1]
    exact M.smul_mem _ hxn

theorem exists_basis_of_anticommute {W : Type*} [AddCommGroup W] [Module ℂ W]
    (hW : Module.finrank ℂ W = 2) (X Y : W →ₗ[ℂ] W) {α β s : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hs : s * s = α)
    (hX : X.comp X = α • LinearMap.id) (hY : Y.comp Y = β • LinearMap.id) (hXY : X.comp Y = -(Y.comp X)) :
    ∃ e : Module.Basis (Fin 2) ℂ W, X (e 0) = s • e 0 ∧ X (e 1) = -(s • e 1) ∧ Y (e 0) = e 1 ∧ Y (e 1) = β • e 0 := by
  have hs0 : s ≠ 0 := fun h => hα (by rw [← hs, h, mul_zero])
  haveI : Module.Finite ℂ W := Module.finite_of_finrank_eq_succ hW
  have hpos : 0 < Module.finrank ℂ W := by omega

  obtain ⟨w₀, hw₀⟩ : ∃ w : W, w ≠ 0 := by
    have : Nontrivial W := Module.nontrivial_of_finrank_pos hpos
    exact exists_ne 0

  have hne : ∃ w : W, X w + s • w ≠ 0 := by
    by_contra h
    push_neg at h
    have hXw : ∀ w, X w = -(s • w) := fun w => eq_neg_of_add_eq_zero_left (h w)

    have hY0 : ∀ w, Y w = 0 := by
      intro w
      have h1 := congrArg (fun f : W →ₗ[ℂ] W => f w) hXY
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, hXw, map_neg, map_smul, neg_neg] at h1

      have h2 : (2 : ℂ) • (s • Y w) = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h1]
        exact neg_add_cancel _
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 two_ne_zero
      · rcases smul_eq_zero.mp h3 with h4 | h4
        · exact absurd h4 hs0
        · exact h4
    have h3 := congrArg (fun f : W →ₗ[ℂ] W => f w₀) hY
    simp only [LinearMap.comp_apply, hY0, map_zero, LinearMap.smul_apply, LinearMap.id_apply] at h3
    exact hw₀ ((smul_eq_zero.mp h3.symm).resolve_left hβ)
  obtain ⟨w, hw⟩ := hne
  set u : W := X w + s • w with hu
  set v : W := Y u with hv
  have hXu : X u = s • u := by
    have h1 := congrArg (fun f : W →ₗ[ℂ] W => f w) hX
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
    simp only [hu, map_add, map_smul, h1, ← hs, smul_add, smul_smul]
    abel
  have hXv : X v = -(s • v) := by
    have h1 := congrArg (fun f : W →ₗ[ℂ] W => f u) hXY
    simp only [LinearMap.comp_apply, LinearMap.neg_apply] at h1
    rw [hv, h1, hXu, map_smul]
  have hYv : Y v = β • u := by
    have h1 := congrArg (fun f : W →ₗ[ℂ] W => f u) hY
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
    rw [hv, h1]
  have hu0 : u ≠ 0 := hw
  have hv0 : v ≠ 0 := by
    intro h
    have : β • u = 0 := by rw [← hYv, h, map_zero]
    exact hu0 ((smul_eq_zero.mp this).resolve_left hβ)
  have hli : LinearIndependent ℂ ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro c d hcd
    have h1 : (c * s) • u - (d * s) • v = 0 := by
      have := congrArg X hcd
      rw [map_add, map_smul, map_smul, hXu, hXv, map_zero, smul_neg, smul_smul, smul_smul, ← sub_eq_add_neg] at this
      exact this
    have h2 : (2 * c * s) • u = 0 := by
      have h3 : s • (c • u + d • v) + ((c * s) • u - (d * s) • v) = 0 := by rw [hcd, h1, smul_zero, zero_add]
      have h4 : s • (c • u + d • v) + ((c * s) • u - (d * s) • v) = (2 * c * s) • u := by
        rw [smul_add, smul_smul, smul_smul]; module
      rw [← h4]; exact h3
    have hc : c = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · simpa [hs0] using h
      · exact absurd h hu0
    refine ⟨hc, ?_⟩
    rw [hc, zero_smul, zero_add] at hcd
    exact (smul_eq_zero.mp hcd).resolve_right hv0
  let e : Module.Basis (Fin 2) ℂ W := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hW])
  have he0 : e 0 = u := by simp [e]
  have he1 : e 1 = v := by simp [e]
  exact ⟨e, by rw [he0, hXu], by rw [he1, hXv], by rw [he0, he1], by rw [he1, he0, hYv]⟩

omit [Fact q.Prime] [Fact q'.Prime] in

theorem quat_decomp (N : ℚ) (hN : N ≠ 0) (y : ℍ[ℚ, a, b]) :
    y.re • (1 : ℍ[ℚ, a, b]) + (y.imI / N) • (⟨0, N, 0, 0⟩ : ℍ[ℚ, a, b]) + (y.imJ / N) • (⟨0, 0, N, 0⟩ : ℍ[ℚ, a, b]) +
        (y.imK / (N * N)) • (⟨0, 0, 0, N * N⟩ : ℍ[ℚ, a, b]) = y := by
  have hNN : N * N ≠ 0 := mul_ne_zero hN hN
  ext <;> simp [div_mul_cancel₀, hN, hNN]

end StdCoord

end

open StdCoord in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (V : Type) [AddCommGroup V] [Module ℂ V] (hV : Module.finrank ℂ V = 2)
    (ρ : ↥Λ → (V →ₗ[ℂ] V))
    (hρ_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, ρ ⟨1, h⟩ = LinearMap.id)
    (hρ_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = (ρ x).comp (ρ y))
    (hρ_add : ∀ x y : ↥Λ, ρ (x + y) = ρ x + ρ y) :
    ∃ P : V ≃ₗ[ℂ] (Fin 2 → ℂ), ∀ (x : ↥Λ) (v : V),
      P (ρ x v) = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (P v) := by
  classical
  obtain ⟨ha, hb⟩ := ne_zero_and_ne_zero hB

  let ρ' : ↥Λ →+ (V →ₗ[ℂ] V) := AddMonoidHom.mk' ρ hρ_add
  have hρ' : ∀ x, ρ' x = ρ x := fun x => rfl

  set qi : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩ with hqi
  set qj : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩ with hqj
  have hmemspan : ∀ y : ℍ[ℚ, a, b], y ∈ Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) := fun y => by
    rw [hΛ.spanTop]; trivial
  obtain ⟨n₁, hn₁, hI₁⟩ := exists_nsmul_mem_of_mem_span Λ (hmemspan qi)
  obtain ⟨n₂, hn₂, hJ₂⟩ := exists_nsmul_mem_of_mem_span Λ (hmemspan qj)
  set N : ℕ := n₁ * n₂ with hN
  have hNpos : 0 < N := Nat.mul_pos hn₁ hn₂
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hNpos.ne'
  set I₀ : ℍ[ℚ, a, b] := (N : ℚ) • qi with hI₀
  set J₀ : ℍ[ℚ, a, b] := (N : ℚ) • qj with hJ₀
  have hI₀mem : I₀ ∈ Λ := by
    have : I₀ = (n₂ : ℤ) • ((n₁ : ℚ) • qi) := by
      rw [hI₀, hN, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]; push_cast; ring
    rw [this]; exact Λ.smul_mem _ hI₁
  have hJ₀mem : J₀ ∈ Λ := by
    have : J₀ = (n₁ : ℤ) • ((n₂ : ℚ) • qj) := by
      rw [hJ₀, hN, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]; push_cast; ring
    rw [this]; exact Λ.smul_mem _ hJ₂

  have hII : I₀ * I₀ = (((N : ℚ) ^ 2 * a) : ℚ) • (1 : ℍ[ℚ, a, b]) := by
    simp only [hI₀, hqi]; ext <;> simp <;> ring
  have hJJ : J₀ * J₀ = (((N : ℚ) ^ 2 * b) : ℚ) • (1 : ℍ[ℚ, a, b]) := by
    simp only [hJ₀, hqj]; ext <;> simp <;> ring
  have hIJ : I₀ * J₀ = -(J₀ * I₀) := by
    simp only [hI₀, hJ₀, hqi, hqj]; ext <;> simp <;> ring
  have hI₀c : I₀ = ⟨0, N, 0, 0⟩ := by simp only [hI₀, hqi]; ext <;> simp
  have hJ₀c : J₀ = ⟨0, 0, N, 0⟩ := by simp only [hJ₀, hqj]; ext <;> simp
  have hK₀c : I₀ * J₀ = ⟨0, 0, 0, (N : ℚ) * N⟩ := by rw [hI₀c, hJ₀c]; ext <;> simp

  have h1mem : (1 : ℍ[ℚ, a, b]) ∈ Λ := hΛ.one_mem
  have hρ_rat : ∀ (r : ℚ) (h : r • (1 : ℍ[ℚ, a, b]) ∈ Λ), ρ ⟨r • 1, h⟩ = (r : ℂ) • LinearMap.id := by
    intro r h
    have hden : (r.den : ℕ) • (⟨r • 1, h⟩ : ↥Λ) = (r.num : ℤ) • (⟨1, h1mem⟩ : ↥Λ) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, Rat.den_mul_eq_num]
    have h2 : (r.den : ℕ) • ρ ⟨r • 1, h⟩ = (r.num : ℤ) • ρ ⟨1, h1mem⟩ := by
      rw [← hρ', ← hρ', ← map_nsmul, ← map_zsmul, hden]
    rw [hρ_one h1mem, ← Nat.cast_smul_eq_nsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ] at h2
    have hd : ((r.den : ℕ) : ℂ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
    have h3 : ρ ⟨r • 1, h⟩ = ((r.den : ℕ) : ℂ)⁻¹ • ((r.num : ℤ) : ℂ) • (LinearMap.id : V →ₗ[ℂ] V) := by
      rw [← h2, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [h3, smul_smul]
    congr 1
    rw [← Rat.num_div_den r]
    push_cast
    rw [Rat.num_div_den r]
    field_simp

  set X : V →ₗ[ℂ] V := ρ ⟨I₀, hI₀mem⟩ with hX
  set Y : V →ₗ[ℂ] V := ρ ⟨J₀, hJ₀mem⟩ with hY
  set α : ℂ := (((N : ℚ) ^ 2 * a : ℚ) : ℂ) with hαdef
  set β : ℂ := (((N : ℚ) ^ 2 * b : ℚ) : ℂ) with hβdef
  have hα0 : α ≠ 0 := by simp only [hαdef]; exact_mod_cast mul_ne_zero (pow_ne_zero 2 hN0) ha
  have hβ0 : β ≠ 0 := by simp only [hβdef]; exact_mod_cast mul_ne_zero (pow_ne_zero 2 hN0) hb
  have hIImem : I₀ * I₀ ∈ Λ := hΛ.mul_mem hI₀mem hI₀mem
  have hJJmem : J₀ * J₀ ∈ Λ := hΛ.mul_mem hJ₀mem hJ₀mem
  have hIJmem : I₀ * J₀ ∈ Λ := hΛ.mul_mem hI₀mem hJ₀mem
  have hJImem : J₀ * I₀ ∈ Λ := hΛ.mul_mem hJ₀mem hI₀mem
  have hXX : X.comp X = α • LinearMap.id := by
    rw [hX, ← hρ_mul _ _ hIImem]
    have : (⟨I₀ * I₀, hIImem⟩ : ↥Λ) = ⟨(((N : ℚ) ^ 2 * a) : ℚ) • 1, hII ▸ hIImem⟩ := Subtype.ext hII
    rw [this, hρ_rat]
  have hYY : Y.comp Y = β • LinearMap.id := by
    rw [hY, ← hρ_mul _ _ hJJmem]
    have : (⟨J₀ * J₀, hJJmem⟩ : ↥Λ) = ⟨(((N : ℚ) ^ 2 * b) : ℚ) • 1, hJJ ▸ hJJmem⟩ := Subtype.ext hJJ
    rw [this, hρ_rat]
  have hXYrel : X.comp Y = -(Y.comp X) := by
    rw [hX, hY, ← hρ_mul _ _ hIJmem, ← hρ_mul _ _ hJImem, ← hρ', ← hρ', ← map_neg]
    congr 1
    exact Subtype.ext hIJ

  set X' : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := Matrix.toLin' (cx (ι I₀)) with hX'
  set Y' : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := Matrix.toLin' (cx (ι J₀)) with hY'
  have hcxrat : ∀ r : ℚ, cx (ι (r • (1 : ℍ[ℚ, a, b]))) = (r : ℂ) • 1 := by
    intro r
    rw [map_smul, map_one, show ((r : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = ((r : ℝ) • 1) from by
      ext i j; simp [Matrix.smul_apply, Rat.smul_def], cx_smul, cx_one, Complex.ofReal_ratCast]
  have hX'X' : X'.comp X' = α • LinearMap.id := by
    rw [hX', ← Matrix.toLin'_mul, ← cx_mul, ← map_mul, hII, hcxrat, map_smul, Matrix.toLin'_one]
  have hY'Y' : Y'.comp Y' = β • LinearMap.id := by
    rw [hY', ← Matrix.toLin'_mul, ← cx_mul, ← map_mul, hJJ, hcxrat, map_smul, Matrix.toLin'_one]
  have hX'Y' : X'.comp Y' = -(Y'.comp X') := by
    rw [hX', hY', ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← cx_mul, ← cx_mul, ← map_mul, ← map_mul, hIJ,
      map_neg, cx_neg, map_neg]

  obtain ⟨s, hs2⟩ := IsAlgClosed.exists_pow_nat_eq α (by norm_num : 0 < 2)
  have hs : s * s = α := by rw [← hs2, pow_two]
  obtain ⟨e, he0X, he1X, he0Y, he1Y⟩ := exists_basis_of_anticommute hV X Y hα0 hβ0 hs hXX hYY hXYrel
  obtain ⟨e', he0X', he1X', he0Y', he1Y'⟩ :=
    exists_basis_of_anticommute (Module.finrank_fin_fun ℂ) X' Y' hα0 hβ0 hs hX'X' hY'Y' hX'Y'
  obtain ⟨P, hP⟩ : ∃ P : V ≃ₗ[ℂ] (Fin 2 → ℂ), ∀ i, P (e i) = e' i :=
    ⟨e.equiv e' (Equiv.refl _), fun i => by simp⟩
  have hPX : ∀ w, P (X w) = X' (P w) := by
    intro w
    have key : ∀ i : Fin 2, (P.toLinearMap.comp X) (e i) = (X'.comp P.toLinearMap) (e i) := by
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · show P (X (e 0)) = X' (P (e 0))
        rw [he0X, map_smul, hP, he0X']
      · show P (X (e 1)) = X' (P (e 1))
        rw [he1X, map_neg, map_smul, hP, he1X']
    exact congrArg (fun f : V →ₗ[ℂ] (Fin 2 → ℂ) => f w) (e.ext key)
  have hPY : ∀ w, P (Y w) = Y' (P w) := by
    intro w
    have key : ∀ i : Fin 2, (P.toLinearMap.comp Y) (e i) = (Y'.comp P.toLinearMap) (e i) := by
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · show P (Y (e 0)) = Y' (P (e 0))
        rw [he0Y, hP, hP, he0Y']
      · show P (Y (e 1)) = Y' (P (e 1))
        rw [he1Y, map_smul, hP, hP, he1Y']
    exact congrArg (fun f : V →ₗ[ℂ] (Fin 2 → ℂ) => f w) (e.ext key)

  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : ↥Λ →+ (V →ₗ[ℂ] (Fin 2 → ℂ)), ∀ x, F₁ x = P.toLinearMap.comp (ρ x) :=
    ⟨{ toFun := fun x => P.toLinearMap.comp (ρ x)
       map_zero' := by
         have : ρ 0 = 0 := by rw [← hρ']; exact map_zero ρ'
         rw [this, LinearMap.comp_zero]
       map_add' := fun x y => by rw [hρ_add, LinearMap.comp_add] }, fun x => rfl⟩
  obtain ⟨F₂, hF₂⟩ : ∃ F₂ : ↥Λ →+ (V →ₗ[ℂ] (Fin 2 → ℂ)),
      ∀ x, F₂ x = (Matrix.toLin' (cx (ι (x : ℍ[ℚ, a, b])))).comp P.toLinearMap :=
    ⟨{ toFun := fun x => (Matrix.toLin' (cx (ι (x : ℍ[ℚ, a, b])))).comp P.toLinearMap
       map_zero' := by simp [cx]
       map_add' := fun x y => by
         rw [Submodule.coe_add, map_add, cx_add, map_add, LinearMap.add_comp] }, fun x => rfl⟩

  obtain ⟨g, hg0, hg1, hg2, hg3⟩ : ∃ g : Fin 4 → ℍ[ℚ, a, b], g 0 = 1 ∧ g 1 = I₀ ∧ g 2 = J₀ ∧ g 3 = I₀ * J₀ :=
    ⟨![1, I₀, J₀, I₀ * J₀], by simp, by simp, by simp, by simp⟩
  have hgmem : ∀ t, g t ∈ Λ := by
    intro t; fin_cases t
    · exact hg0 ▸ h1mem
    · exact hg1 ▸ hI₀mem
    · exact hg2 ▸ hJ₀mem
    · exact hg3 ▸ hIJmem
  have hA0 : F₁ ⟨1, h1mem⟩ = F₂ ⟨1, h1mem⟩ := by
    rw [hF₁, hF₂, hρ_one, map_one, cx_one, Matrix.toLin'_one]; rfl
  have hA1 : F₁ ⟨I₀, hI₀mem⟩ = F₂ ⟨I₀, hI₀mem⟩ := by
    rw [hF₁, hF₂]; exact LinearMap.ext fun w => hPX w
  have hA2 : F₁ ⟨J₀, hJ₀mem⟩ = F₂ ⟨J₀, hJ₀mem⟩ := by
    rw [hF₁, hF₂]; exact LinearMap.ext fun w => hPY w
  have hA3 : F₁ ⟨I₀ * J₀, hIJmem⟩ = F₂ ⟨I₀ * J₀, hIJmem⟩ := by
    rw [hF₁, hF₂, show ρ ⟨I₀ * J₀, hIJmem⟩ = X.comp Y from hρ_mul ⟨I₀, hI₀mem⟩ ⟨J₀, hJ₀mem⟩ hIJmem,
      map_mul, cx_mul, Matrix.toLin'_mul]
    refine LinearMap.ext fun w => ?_
    show P (X (Y w)) = X' (Y' (P w))
    rw [hPX, hPY]
  have hagree : ∀ t, F₁ ⟨g t, hgmem t⟩ = F₂ ⟨g t, hgmem t⟩ := by
    intro t
    fin_cases t
    · change F₁ ⟨g 0, hgmem 0⟩ = F₂ ⟨g 0, hgmem 0⟩
      rw [show (⟨g 0, hgmem 0⟩ : ↥Λ) = ⟨1, h1mem⟩ from Subtype.ext hg0]; exact hA0
    · change F₁ ⟨g 1, hgmem 1⟩ = F₂ ⟨g 1, hgmem 1⟩
      rw [show (⟨g 1, hgmem 1⟩ : ↥Λ) = ⟨I₀, hI₀mem⟩ from Subtype.ext hg1]; exact hA1
    · change F₁ ⟨g 2, hgmem 2⟩ = F₂ ⟨g 2, hgmem 2⟩
      rw [show (⟨g 2, hgmem 2⟩ : ↥Λ) = ⟨J₀, hJ₀mem⟩ from Subtype.ext hg2]; exact hA2
    · change F₁ ⟨g 3, hgmem 3⟩ = F₂ ⟨g 3, hgmem 3⟩
      rw [show (⟨g 3, hgmem 3⟩ : ↥Λ) = ⟨I₀ * J₀, hIJmem⟩ from Subtype.ext hg3]; exact hA3

  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : Submodule ℤ ℍ[ℚ, a, b], Λ₀ = Submodule.span ℤ (Set.range g) := ⟨_, rfl⟩
  have hΛ₀le : Λ₀ ≤ Λ := by
    rw [hΛ₀]; exact Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hgmem t)
  have hagree₀ : ∀ z (hz : z ∈ Λ₀), F₁ ⟨z, hΛ₀le hz⟩ = F₂ ⟨z, hΛ₀le hz⟩ := by
    intro z hz
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hΛ₀ ▸ hz)
    have hz' : (⟨z, hΛ₀le hz⟩ : ↥Λ) = ∑ t, c t • (⟨g t, hgmem t⟩ : ↥Λ) := by
      apply Subtype.ext
      show z = ((∑ t, c t • (⟨g t, hgmem t⟩ : ↥Λ) : ↥Λ) : ℍ[ℚ, a, b])
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [Submodule.coe_smul]
      exact hc.symm
    rw [hz', map_sum, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_zsmul, map_zsmul, hagree t]

  have hspan₀ : ∀ y : ℍ[ℚ, a, b], y ∈ Submodule.span ℚ (Λ₀ : Set ℍ[ℚ, a, b]) := by
    intro y
    have hsub : ∀ t, g t ∈ Submodule.span ℚ (Λ₀ : Set ℍ[ℚ, a, b]) := fun t =>
      Submodule.subset_span (by rw [hΛ₀]; exact Submodule.subset_span (Set.mem_range_self t))
    have hmem : y.re • (1 : ℍ[ℚ, a, b]) + (y.imI / N) • I₀ + (y.imJ / N) • J₀ +
        (y.imK / ((N : ℚ) * N)) • (I₀ * J₀) ∈ Submodule.span ℚ (Λ₀ : Set ℍ[ℚ, a, b]) := by
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
      · exact Submodule.smul_mem _ _ (hg0 ▸ hsub 0)
      · exact Submodule.smul_mem _ _ (hg1 ▸ hsub 1)
      · exact Submodule.smul_mem _ _ (hg2 ▸ hsub 2)
      · exact Submodule.smul_mem _ _ (hg3 ▸ hsub 3)
    rw [hK₀c, hI₀c, hJ₀c, quat_decomp (N : ℚ) hN0 y] at hmem
    exact hmem

  have hall : ∀ x : ↥Λ, F₁ x = F₂ x := by
    intro x
    obtain ⟨D, hD, hDx⟩ := exists_nsmul_mem_of_mem_span Λ₀ (hspan₀ (x : ℍ[ℚ, a, b]))
    have hDx' : (D : ℕ) • x = ⟨((D : ℚ) • (x : ℍ[ℚ, a, b])), hΛ₀le hDx⟩ := by
      apply Subtype.ext
      show ((D • x : ↥Λ) : ℍ[ℚ, a, b]) = (D : ℚ) • (x : ℍ[ℚ, a, b])
      rw [Nat.cast_smul_eq_nsmul]
      exact map_nsmul Λ.subtype D x
    have h1 : (D : ℕ) • F₁ x = (D : ℕ) • F₂ x := by
      rw [← map_nsmul, ← map_nsmul, hDx']
      exact hagree₀ _ hDx
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h1
    exact smul_right_injective _ (show ((D : ℕ) : ℂ) ≠ 0 by exact_mod_cast hD.ne') h1
  refine ⟨P, fun x v => ?_⟩
  have h := congrArg (fun f : V →ₗ[ℂ] (Fin 2 → ℂ) => f v) (hall x)
  simp only [hF₁, hF₂, LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply] at h
  exact h

end S_QuaternionAlgebra_IsOrder_exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_linearEquiv_apply_eq_mulVec_map_of_finrank_eq_two (solution)
