-- Prove2me | solution 1 for PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/015aced2-d76c-55bc-85a5-4ec5ad3ff471

import Mathlib
import Theorems.Thm_WLight_weierstrassP_qExpansion_package
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty

set_option autoImplicit false

open scoped MatrixGroups CongruenceSubgroup ModularForm Topology Manifold Matrix Real
p2m_open "UpperHalfPlane~I"
open Complex Filter

noncomputable section

namespace EIS2K1

variable (L : ℍ → PeriodPair) {N : ℕ}

def W (N : ℕ) (b : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  (L τ).weierstrassP ((((b 0).val : ℂ) * (τ : ℂ) + (b 1).val) / N)

abbrev redN (N : ℕ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))

lemma redN_apply (γ : SL(2, ℤ)) (i j : Fin 2) : redN N γ i j = ((γ i j : ℤ) : ZMod N) := rfl

section Lattice

variable {L} (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
include hL

omit hL in

lemma weierstrassP_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) : L₁.weierstrassP = L₂.weierstrassP := by
  funext z
  simp only [PeriodPair.weierstrassP]
  rw [h]

omit hL in
lemma indep_of_im_ne_zero {τ : ℂ} (hτ : τ.im ≠ 0) (γ : SL(2, ℤ)) :
    LinearIndependent ℝ ![((γ 0 0 : ℤ) : ℂ) * τ + (γ 0 1 : ℤ), ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
    rw [γ.prop] at this
    linarith

  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.smul_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero, smul_eq_mul, Complex.zero_im, Complex.add_re, Complex.smul_re, Complex.mul_re,
    sub_zero, Complex.zero_re] at him hre
  have h1 : (s * (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ)) * τ.im = 0 := by
    have : s * ((γ 0 0 : ℤ) * τ.im) + t * ((γ 1 0 : ℤ) * τ.im) = 0 := by exact_mod_cast him
    linarith
  have hA : s * (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hτ
  have hB : s * (γ 0 1 : ℤ) + t * (γ 1 1 : ℤ) = 0 := by
    have : s * ((γ 0 0 : ℤ) * τ.re + (γ 0 1 : ℤ)) + t * ((γ 1 0 : ℤ) * τ.re + (γ 1 1 : ℤ)) = 0 := by
      exact_mod_cast hre
    have h2 : (s * (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ)) * τ.re + (s * (γ 0 1 : ℤ) + t * (γ 1 1 : ℤ)) = 0 := by
      linarith
    rwa [hA, zero_mul, zero_add] at h2
  have hd : ((γ 0 0 : ℤ) : ℝ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by exact_mod_cast hdet
  constructor
  · have : s = (s * (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ)) * (γ 1 1 : ℤ) - (s * (γ 0 1 : ℤ) + t * (γ 1 1 : ℤ)) * (γ 1 0 : ℤ) := by
      linear_combination (-s) * hd
    rw [this, hA, hB]; ring
  · have : t = -(s * (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ)) * (γ 0 1 : ℤ) + (s * (γ 0 1 : ℤ) + t * (γ 1 1 : ℤ)) * (γ 0 0 : ℤ) := by
      linear_combination (-t) * hd
    rw [this, hA, hB]; ring

omit hL in

def pairγ (γ : SL(2, ℤ)) (τ : ℍ) : PeriodPair :=
  ⟨((γ 0 0 : ℤ) : ℂ) * τ + (γ 0 1 : ℤ), ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ), indep_of_im_ne_zero τ.im_ne_zero γ⟩

lemma lattice_L (τ : ℍ) : (L τ).lattice = Submodule.span ℤ {(τ : ℂ), 1} := by
  rw [PeriodPair.lattice, (hL τ).1, (hL τ).2]

lemma lattice_pairγ (γ : SL(2, ℤ)) (τ : ℍ) : (pairγ γ τ).lattice = (L τ).lattice := by
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
    rw [γ.prop] at this
    linarith
  rw [lattice_L hL, PeriodPair.lattice]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · rw [pairγ, SetLike.mem_coe, Submodule.mem_span_pair]
      exact ⟨γ 0 0, γ 0 1, by simp [zsmul_eq_mul]⟩
    · rw [pairγ, SetLike.mem_coe, Submodule.mem_span_pair]
      exact ⟨γ 1 0, γ 1 1, by simp [zsmul_eq_mul]⟩
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, Submodule.mem_span_pair]
      refine ⟨γ 1 1, -(γ 0 1), ?_⟩
      simp only [pairγ, zsmul_eq_mul, Int.cast_neg]
      have hd : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by exact_mod_cast hdet
      linear_combination (τ : ℂ) * hd
    · rw [SetLike.mem_coe, Submodule.mem_span_pair]
      refine ⟨-(γ 1 0), γ 0 0, ?_⟩
      simp only [pairγ, zsmul_eq_mul, Int.cast_neg]
      have hd : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by exact_mod_cast hdet
      linear_combination hd

lemma weierstrassP_add_int (τ : ℍ) (z : ℂ) (m n : ℤ) :
    (L τ).weierstrassP (z + ((m : ℂ) * τ + n)) = (L τ).weierstrassP z := by
  have hmem : ((m : ℂ) * τ + n) ∈ (L τ).lattice := by
    rw [PeriodPair.mem_lattice]
    exact ⟨m, n, by rw [(hL τ).1, (hL τ).2, mul_one]⟩
  exact (L τ).weierstrassP_add_coe z ⟨_, hmem⟩

end Lattice

section Slash

variable {L} (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) [NeZero N]
include hL

lemma W_smul (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    W L N a (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ)) ^ 2 *
      (L τ).weierstrassP
        (((((a 0).val * γ 0 0 + (a 1).val * γ 1 0 : ℤ) : ℂ) * τ + ((a 0).val * γ 0 1 + (a 1).val * γ 1 1 : ℤ)) / N) := by
  obtain ⟨-, -, -, -, h4⟩ := WLight.weierstrassP_qExpansion_package
  set de : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ) with hde
  set nu : ℂ := ((γ 0 0 : ℤ) : ℂ) * τ + (γ 0 1 : ℤ) with hnu
  have hde0 : de ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ τ
    simpa [denom, hde] using this
  have hcoe : ((γ • τ : ℍ) : ℂ) = nu / de := by
    simp [UpperHalfPlane.specialLinearGroup_apply, hnu, hde]

  have h1 : (L (γ • τ)).ω₁ = de⁻¹ * (pairγ γ τ).ω₁ := by
    rw [(hL _).1, hcoe]; simp only [pairγ]; rw [div_eq_inv_mul]
  have h2 : (L (γ • τ)).ω₂ = de⁻¹ * (pairγ γ τ).ω₂ := by
    rw [(hL _).2]; simp only [pairγ]; rw [← hde, inv_mul_cancel₀ hde0]
  set z : ℂ := ((((a 0).val * γ 0 0 + (a 1).val * γ 1 0 : ℤ) : ℂ) * τ +
      ((a 0).val * γ 0 1 + (a 1).val * γ 1 1 : ℤ)) / N with hz
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have harg : ((((a 0).val : ℂ) * ((γ • τ : ℍ) : ℂ) + (a 1).val) / N) = de⁻¹ * z := by
    rw [hcoe, hz]
    field_simp
    rw [hnu, hde]
    push_cast
    ring
  rw [W, harg, h4 (pairγ γ τ) (L (γ • τ)) de⁻¹ h1 h2 z, inv_inv, weierstrassP_congr (lattice_pairγ hL γ τ)]

theorem W_slash (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : W L N a ∣[(2 : ℤ)] γ = W L N (a ᵥ* redN N γ) := by
  funext τ
  rw [ModularForm.SL_slash_apply, W_smul hL a γ τ]
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) τ
      = ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ) := by
    simp [denom]
  have hde0 : ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ) ≠ 0 := by
    rw [← hden]; exact UpperHalfPlane.denom_ne_zero _ τ
  rw [hden, mul_comm, ← mul_assoc, show (-(2 : ℤ)) = -((2 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero 2 hde0), one_mul]

  set A : ℤ := (a 0).val * γ 0 0 + (a 1).val * γ 1 0 with hA
  set B : ℤ := (a 0).val * γ 0 1 + (a 1).val * γ 1 1 with hB
  have hA' : (((a ᵥ* redN N γ) 0).val : ZMod N) = (A : ZMod N) := by
    rw [ZMod.natCast_zmod_val]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, redN_apply, hA, ZMod.natCast_zmod_val]
  have hB' : (((a ᵥ* redN N γ) 1).val : ZMod N) = (B : ZMod N) := by
    rw [ZMod.natCast_zmod_val]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, redN_apply, hB, ZMod.natCast_zmod_val]
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (((a ᵥ* redN N γ) 0).val : ℤ) = A + N * m := by
    have : ((((((a ᵥ* redN N γ) 0).val : ℤ) - A : ℤ)) : ZMod N) = 0 := by
      push_cast; rw [hA', sub_self]
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    exact ⟨m, by linarith⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (((a ᵥ* redN N γ) 1).val : ℤ) = B + N * n := by
    have : ((((((a ᵥ* redN N γ) 1).val : ℤ) - B : ℤ)) : ZMod N) = 0 := by
      push_cast; rw [hB', sub_self]
    obtain ⟨n, hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    exact ⟨n, by linarith⟩
  rw [W]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hval0 : (((a ᵥ* redN N γ) 0).val : ℂ) = ((A + N * m : ℤ) : ℂ) := by rw [← hm]; norm_cast
  have hval1 : (((a ᵥ* redN N γ) 1).val : ℂ) = ((B + N * n : ℤ) : ℂ) := by rw [← hn]; norm_cast
  rw [hval0, hval1]
  have : (((A + N * m : ℤ) : ℂ) * (τ : ℂ) + ((B + N * n : ℤ) : ℂ)) / N
      = (((A : ℂ)) * τ + B) / N + ((m : ℂ) * τ + n) := by
    push_cast; field_simp; ring
  rw [this, weierstrassP_add_int hL]

end Slash

section Limit

variable [NeZero N]

def qN (N : ℕ) (τ : ℍ) : ℂ := cexp (2 * π * I * (τ : ℂ) / N)

lemma norm_qN (τ : ℍ) : ‖qN N τ‖ = Real.exp (-(2 * π * τ.im / N)) := by
  rw [qN, Complex.norm_exp]
  congr 1
  have : (2 * π * I * (τ : ℂ) / N) = ((-(2 * π * τ.im / N) : ℝ) : ℂ) + ((2 * π * τ.re / N : ℝ) : ℂ) * I := by
    have hτ : (τ : ℂ) = ((τ.re : ℝ) : ℂ) + ((τ.im : ℝ) : ℂ) * I := (Complex.re_add_im (τ : ℂ)).symm
    rw [hτ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]

lemma tendsto_qN : Tendsto (qN N) atImInfty (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_qN]
  have hc : 0 < 2 * π / (N : ℝ) := by
    have := NeZero.pos N
    positivity
  have h1 : Tendsto (fun τ : ℍ => -(2 * π * τ.im / N)) atImInfty atBot := by
    have h2 : Tendsto (fun τ : ℍ => (2 * π / N) * τ.im) atImInfty atTop := by
      rw [atImInfty]
      exact (tendsto_comap).const_mul_atTop hc
    have := tendsto_neg_atTop_atBot.comp h2
    refine this.congr fun τ => ?_
    simp only [Function.comp_apply]; ring
  exact Real.tendsto_exp_atBot.comp h1

def ρ (N : ℕ) : ℝ := Real.exp (-(2 * π / N))

lemma ρ_pos : 0 < ρ N := Real.exp_pos _

lemma ρ_lt_one : ρ N < 1 := by
  have := NeZero.pos N
  have h : -(2 * π / (N : ℝ)) < 0 := by
    have : 0 < 2 * π / (N : ℝ) := by positivity
    linarith
  calc ρ N < Real.exp 0 := Real.exp_lt_exp.mpr h
    _ = 1 := Real.exp_zero

lemma norm_qN_le {τ : ℍ} (hτ : 1 ≤ τ.im) : ‖qN N τ‖ ≤ ρ N := by
  rw [norm_qN, ρ, Real.exp_le_exp, neg_le_neg_iff]
  have := NeZero.pos N
  have h : 2 * π / (N : ℝ) * 1 ≤ 2 * π / N * τ.im := mul_le_mul_of_nonneg_left hτ (by positivity)
  calc 2 * π / (N : ℝ) = 2 * π / N * 1 := by ring
    _ ≤ 2 * π / N * τ.im := h
    _ = 2 * π * τ.im / N := by ring

def ζ (N : ℕ) : ℂ := cexp (2 * π * I / N)

lemma norm_ζ : ‖ζ N‖ = 1 := by
  rw [ζ, show (2 * π * I / N : ℂ) = ((2 * π / N : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_ζ_pow (k : ℕ) : ‖ζ N ^ k‖ = 1 := by rw [norm_pow, norm_ζ, one_pow]

lemma norm_ζ_inv_pow (k : ℕ) : ‖(ζ N)⁻¹ ^ k‖ = 1 := by rw [norm_pow, norm_inv, norm_ζ, inv_one, one_pow]

def term (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℍ) : ℂ :=
  ((p.2 : ℕ) : ℂ) *
    (ζ N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (ζ N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
      2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ)))

def bound (N : ℕ) (p : ℕ+ × ℕ+) : ℝ := (4 * ρ N ^ ((p.1 : ℕ) - 1)) * (((p.2 : ℕ) : ℝ) * ρ N ^ (p.2 : ℕ))

lemma summable_bound : Summable (bound N) := by
  have hρ := ρ_lt_one (N := N)
  have hρ0 := (ρ_pos (N := N)).le
  have h1 : Summable fun p : ℕ+ => 4 * ρ N ^ ((p : ℕ) - 1) := by
    have hg : Summable fun n : ℕ => ρ N ^ n := summable_geometric_of_lt_one hρ0 hρ
    have : Summable fun p : ℕ+ => ρ N ^ ((p : ℕ) - 1) := by
      have := hg.comp_injective (i := fun p : ℕ+ => (p : ℕ) - 1) (fun p q h => by
        have hp := p.pos; have hq := q.pos
        exact PNat.eq (by simp only at h; omega))
      exact this
    exact this.mul_left 4
  have h2 : Summable fun p : ℕ+ => ((p : ℕ) : ℝ) * ρ N ^ (p : ℕ) := by
    have hg : Summable fun n : ℕ => (n : ℝ) ^ 1 * ρ N ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ)
    have := hg.comp_injective PNat.coe_injective
    simp at this
    exact this
  exact h1.mul_of_nonneg h2 (fun p => by positivity) (fun p => by positivity)

lemma exp_le (a₁ : ℕ) (ha₁ : a₁ < N) (p : ℕ+ × ℕ+) :
    (p.1 : ℕ) - 1 + (p.2 : ℕ) ≤ ((p.1 : ℕ) * N - a₁) * (p.2 : ℕ) ∧
    (p.1 : ℕ) - 1 + (p.2 : ℕ) ≤ ((p.1 : ℕ) * N + a₁) * (p.2 : ℕ) ∧
    (p.1 : ℕ) - 1 + (p.2 : ℕ) ≤ (p.1 : ℕ) * N * (p.2 : ℕ) := by
  have hp1 := p.1.pos
  have hp2 := p.2.pos
  set x : ℕ := (p.1 : ℕ) with hx
  set y : ℕ := (p.2 : ℕ) with hy
  have hxy : x - 1 + y ≤ x * y := by
    have : (x - 1) * 1 ≤ (x - 1) * y := Nat.mul_le_mul_left _ hp2
    have h' : x * y = (x - 1) * y + y := by
      rcases x with _ | x
      · omega
      · simp [Nat.succ_sub_one, Nat.succ_mul]
    omega
  have hxN : x ≤ x * N - a₁ := by
    have : x * N ≥ x + a₁ := by
      have hN1 : 1 + a₁ ≤ N := by omega
      calc x + a₁ ≤ x + x * a₁ := by nlinarith
        _ = x * (1 + a₁) := by ring
        _ ≤ x * N := Nat.mul_le_mul_left _ hN1
    omega
  refine ⟨le_trans hxy (Nat.mul_le_mul_right _ hxN), le_trans hxy (Nat.mul_le_mul_right _ ?_),
    le_trans hxy (Nat.mul_le_mul_right _ ?_)⟩
  · have := NeZero.pos N; nlinarith
  · have := NeZero.pos N; nlinarith

lemma norm_term_le (a₁ a₂ : ℕ) (ha₁ : a₁ < N) (p : ℕ+ × ℕ+) {τ : ℍ} (hτ : 1 ≤ τ.im) :
    ‖term N a₁ a₂ p τ‖ ≤ bound N p := by
  have hρ1 := (ρ_lt_one (N := N)).le
  have hρ0 := (ρ_pos (N := N)).le
  have hq : ‖qN N τ‖ ≤ ρ N := norm_qN_le hτ
  have hq0 : 0 ≤ ‖qN N τ‖ := norm_nonneg _
  obtain ⟨e1, e2, e3⟩ := exp_le a₁ ha₁ p (N := N)

  have hpow : ∀ e : ℕ, (p.1 : ℕ) - 1 + (p.2 : ℕ) ≤ e → ‖qN N τ ^ e‖ ≤ ρ N ^ ((p.1 : ℕ) - 1 + (p.2 : ℕ)) := by
    intro e he
    rw [norm_pow]
    calc ‖qN N τ‖ ^ e ≤ ρ N ^ e := pow_le_pow_left₀ hq0 hq e
      _ ≤ ρ N ^ ((p.1 : ℕ) - 1 + (p.2 : ℕ)) := pow_le_pow_of_le_one hρ0 hρ1 he
  set R : ℝ := ρ N ^ ((p.1 : ℕ) - 1 + (p.2 : ℕ)) with hR
  have hA : ‖ζ N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ))‖ ≤ R := by
    rw [norm_mul, norm_ζ_pow, one_mul]; exact hpow _ e2
  have hB : ‖(ζ N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ))‖ ≤ R := by
    rw [norm_mul, norm_ζ_inv_pow, one_mul]; exact hpow _ e1
  have hC : ‖2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ))‖ ≤ 2 * R := by
    rw [norm_mul, Complex.norm_two]; exact mul_le_mul_of_nonneg_left (hpow _ e3) zero_le_two
  rw [term, norm_mul, Complex.norm_natCast]
  have hsum : ‖ζ N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (ζ N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
      2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ))‖ ≤ 4 * R := by
    calc _ ≤ ‖ζ N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
          (ζ N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ))‖ +
          ‖2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ))‖ := norm_sub_le _ _
      _ ≤ (R + R) + 2 * R := add_le_add ((norm_add_le _ _).trans (add_le_add hA hB)) hC
      _ = 4 * R := by ring
  calc ((p.2 : ℕ) : ℝ) * _ ≤ ((p.2 : ℕ) : ℝ) * (4 * R) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = bound N p := by rw [bound, hR, pow_add]; ring

lemma tendsto_term (a₁ a₂ : ℕ) (ha₁ : a₁ < N) (p : ℕ+ × ℕ+) :
    Tendsto (fun τ => term N a₁ a₂ p τ) atImInfty (𝓝 0) := by
  obtain ⟨e1, e2, e3⟩ := exp_le a₁ ha₁ p (N := N)
  have hpos : 0 < (p.1 : ℕ) - 1 + (p.2 : ℕ) := by have := p.2.pos; omega
  have hq : ∀ e : ℕ, (p.1 : ℕ) - 1 + (p.2 : ℕ) ≤ e → Tendsto (fun τ => qN N τ ^ e) atImInfty (𝓝 0) := by
    intro e he
    have := (tendsto_qN (N := N)).pow e
    rwa [zero_pow (by omega)] at this
  have h := ((((hq _ e2).const_mul (ζ N ^ (a₂ * (p.2 : ℕ)))).add ((hq _ e1).const_mul ((ζ N)⁻¹ ^ (a₂ * (p.2 : ℕ))))).sub
    ((hq _ e3).const_mul 2)).const_mul (((p.2 : ℕ) : ℂ))
  simp only [mul_zero, add_zero, sub_zero] at h
  exact h

lemma tendsto_tsum_term (a₁ a₂ : ℕ) (ha₁ : a₁ < N) :
    Tendsto (fun τ => ∑' p : ℕ+ × ℕ+, term N a₁ a₂ p τ) atImInfty (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty) (f := fun τ p => term N a₁ a₂ p τ)
    (g := fun _ => (0 : ℂ)) (bound := bound N) summable_bound (fun p => tendsto_term a₁ a₂ ha₁ p) ?_
  · simpa using h
  · have hev : ∀ᶠ τ : ℍ in atImInfty, (1 : ℝ) ≤ τ.im := (atImInfty_mem _).mpr ⟨1, fun _ h => h⟩
    filter_upwards [hev] with τ hτ p
    exact norm_term_le a₁ a₂ ha₁ p hτ

lemma tendsto_A (a₁ a₂ : ℕ) :
    Tendsto (fun τ => ζ N ^ a₂ * qN N τ ^ a₁ / (1 - ζ N ^ a₂ * qN N τ ^ a₁) ^ 2) atImInfty
      (𝓝 (if a₁ = 0 then ζ N ^ a₂ / (1 - ζ N ^ a₂) ^ 2 else 0)) := by
  by_cases ha : a₁ = 0
  · subst ha
    simp only [pow_zero, mul_one, if_true]
    exact tendsto_const_nhds
  · rw [if_neg ha]
    have hq : Tendsto (fun τ => ζ N ^ a₂ * qN N τ ^ a₁) atImInfty (𝓝 0) := by
      have := ((tendsto_qN (N := N)).pow a₁).const_mul (ζ N ^ a₂)
      rwa [zero_pow ha, mul_zero] at this
    have hden : Tendsto (fun τ => (1 - ζ N ^ a₂ * qN N τ ^ a₁) ^ 2) atImInfty (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℂ))).sub hq).pow 2
      simpa using this
    have := hq.div hden one_ne_zero
    simp at this
    exact this

lemma csc_identity (θ : ℂ) (hs : Complex.sin θ ≠ 0) :
    (2 * π * I) ^ 2 * (cexp (2 * (θ * I)) / (1 - cexp (2 * (θ * I))) ^ 2) = (π : ℂ) ^ 2 / Complex.sin θ ^ 2 := by
  set u : ℂ := cexp (θ * I) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hsin : Complex.sin θ = (u⁻¹ - u) * I / 2 := by
    have := Complex.two_sin θ
    rw [show -θ * I = -(θ * I) by ring, Complex.exp_neg, ← hu] at this
    linear_combination this / 2
  have h2 : cexp (2 * (θ * I)) = u ^ 2 := by rw [hu, ← Complex.exp_nat_mul]; norm_num
  have hden : 1 - u ^ 2 ≠ 0 := by
    intro h
    apply hs
    rw [hsin]
    have : u⁻¹ - u = u⁻¹ * (1 - u ^ 2) := by field_simp
    rw [this, h]; simp
  have hsub : u⁻¹ - u ≠ 0 := by
    intro h
    apply hden
    have : u⁻¹ = u := sub_eq_zero.mp h
    have h' : u * u⁻¹ = u * u := by rw [this]
    rw [mul_inv_cancel₀ hu0] at h'
    linear_combination h'
  have hsin2 : Complex.sin θ ^ 2 = -(u⁻¹ - u) ^ 2 / 4 := by
    rw [hsin, div_pow, mul_pow, Complex.I_sq]; ring
  have hI2 : (2 * π * I) ^ 2 = -4 * (π : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [h2, hI2, hsin2]
  field_simp

lemma sin_ne_zero {t : ℕ} (ht0 : t ≠ 0) (htN : t < N) : Complex.sin (π * t / N) ≠ 0 := by
  intro h
  rw [Complex.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (t : ℂ) = (k : ℂ) * N := by
    have h0 : (π : ℂ) * t = k * π * N := (div_eq_iff hN).mp hk
    exact mul_left_cancel₀ hpi (by rw [h0]; ring)
  have h2 : (t : ℤ) = k * N := by exact_mod_cast h1
  have hk0 : 0 < k := by
    by_contra hle
    push Not at hle
    have : (t : ℤ) ≤ 0 := by rw [h2]; exact mul_nonpos_of_nonpos_of_nonneg hle (by positivity)
    omega
  have : (N : ℤ) ≤ t := by rw [h2]; nlinarith
  omega

variable {L} (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
include hL

theorem tendsto_W (a : Fin 2 → ZMod N) (ha : a ≠ 0) :
    Tendsto (W L N a) atImInfty
      (𝓝 (-((π : ℂ) ^ 2 / 3) + if a 0 = 0 then (π : ℂ) ^ 2 / Complex.sin (π * (a 1).val / N) ^ 2 else 0)) := by
  obtain ⟨-, -, -, h23, -⟩ := WLight.weierstrassP_qExpansion_package
  set a₁ : ℕ := (a 0).val with ha₁
  set a₂ : ℕ := (a 1).val with ha₂
  have ha₁N : a₁ < N := ZMod.val_lt _
  have ha₂N : a₂ < N := ZMod.val_lt _
  have hne : a₁ ≠ 0 ∨ a₂ ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp h.1
    · exact (ZMod.val_eq_zero _).mp h.2
  obtain ⟨hexp, -⟩ := h23 L hL N a₁ a₂ ha₁N ha₂N hne

  have hW : W L N a = fun τ => (2 * π * I) ^ 2 *
      (ζ N ^ a₂ * qN N τ ^ a₁ / (1 - ζ N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 + ∑' p : ℕ+ × ℕ+, term N a₁ a₂ p τ) := by
    funext τ
    rw [W, ← ha₁, ← ha₂, hexp τ]
    rfl
  rw [hW]
  have hlim := (((tendsto_A a₁ a₂ (N := N)).add (tendsto_const_nhds (x := (1 / 12 : ℂ)))).add
    (tendsto_tsum_term a₁ a₂ ha₁N)).const_mul ((2 * π * I) ^ 2)
  refine hlim.congr' (Eventually.of_forall fun τ => rfl) |>.trans ?_

  apply le_of_eq
  congr 1
  rw [add_zero]
  have hval0 : a 0 = 0 ↔ a₁ = 0 := (ZMod.val_eq_zero (a 0)).symm
  by_cases h0 : a₁ = 0
  · rw [if_pos h0, if_pos (hval0.mpr h0)]
    have ha₂0 : a₂ ≠ 0 := hne.resolve_left (not_not.mpr h0)
    have hs := sin_ne_zero (N := N) ha₂0 ha₂N
    have hζ : ζ N ^ a₂ = cexp (2 * ((π * a₂ / N) * I)) := by
      rw [ζ, ← Complex.exp_nat_mul]
      congr 1
      ring
    rw [mul_add, hζ, csc_identity _ hs]
    have hI : (2 * π * I) ^ 2 = -4 * (π : ℂ) ^ 2 := by
      rw [mul_pow, Complex.I_sq]; ring
    rw [hI]
    ring
  · rw [if_neg h0, if_neg (fun h => h0 (hval0.mp h))]
    rw [mul_pow, Complex.I_sq]
    ring

end Limit

section MF

variable {L} (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) [NeZero N]
include hL

lemma W_zero : W L N 0 = 0 := by
  funext τ
  simp [W, PeriodPair.weierstrassP_zero]

lemma mdifferentiable_W (a : Fin 2 → ZMod N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (W L N a) := by
  by_cases ha : a = 0
  · subst ha
    rw [W_zero hL]
    exact mdifferentiable_const
  · obtain ⟨-, -, -, h23, -⟩ := WLight.weierstrassP_qExpansion_package
    have hne : (a 0).val ≠ 0 ∨ (a 1).val ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      funext i
      fin_cases i
      · exact (ZMod.val_eq_zero _).mp h.1
      · exact (ZMod.val_eq_zero _).mp h.2
    exact (h23 L hL N (a 0).val (a 1).val (ZMod.val_lt _) (ZMod.val_lt _) hne).2

lemma isBoundedAtImInfty_W (a : Fin 2 → ZMod N) : IsBoundedAtImInfty (W L N a) := by
  by_cases ha : a = 0
  · subst ha
    rw [W_zero hL]
    exact UpperHalfPlane.zero_form_isBoundedAtImInfty
  · exact (tendsto_W hL a ha).isBigO_one ℝ

def sif (a : Fin 2 → ZMod N) : SlashInvariantForm Γ(N) 2 where
  toFun := W L N a
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ Γ(N)), rfl⟩ := hA
    have h := W_slash hL a A
    have hred : redN N A = 1 := by
      rw [redN, CongruenceSubgroup.Gamma_mem'.mp hA]; rfl
    rw [hred, Matrix.vecMul_one] at h
    simpa [Matrix.SpecialLinearGroup.mapGL, ← ModularForm.SL_slash] using h

def mf (a : Fin 2 → ZMod N) : ModularForm Γ(N) 2 where
  toFun := W L N a
  slash_action_eq' := (sif hL a).slash_action_eq'
  holo' := mdifferentiable_W hL a
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    show IsBoundedAtImInfty (W L N a ∣[(2 : ℤ)] γ)
    rw [W_slash hL]
    exact isBoundedAtImInfty_W hL _

theorem main (a : Fin 2 → ZMod N) :
    (∃ F : ModularForm Γ(N) 2, ⇑F = W L N a) ∧
    (∀ γ : SL(2, ℤ), W L N a ∣[(2 : ℤ)] γ = W L N (a ᵥ* redN N γ)) ∧
    (a ≠ 0 → Tendsto (W L N a) atImInfty
      (𝓝 (-((π : ℂ) ^ 2 / 3) + if a 0 = 0 then (π : ℂ) ^ 2 / Complex.sin (π * (a 1).val / N) ^ 2 else 0))) :=
  ⟨⟨mf hL a, rfl⟩, W_slash hL a, tendsto_W hL a⟩

end MF

end EIS2K1

end

theorem solution
    (L : UpperHalfPlane → PeriodPair) (hL : ∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (N : ℕ) [NeZero N] (a : Fin 2 → ZMod N) :
    let W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ :=
      fun b τ => (L τ).weierstrassP ((((b 0).val : ℂ) * (τ : ℂ) + (b 1).val) / N)
    (∃ F : ModularForm (CongruenceSubgroup.Gamma N) 2, ⇑F = W a) ∧
    (∀ γ : SL(2, ℤ), W a ∣[(2 : ℤ)] γ = W (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) ∧
    (a ≠ 0 → Filter.Tendsto (W a) UpperHalfPlane.atImInfty
      (𝓝 (-((π : ℂ) ^ 2 / 3) + if a 0 = 0 then (π : ℂ) ^ 2 / Complex.sin (π * (a 1).val / N) ^ 2 else 0))) :=
  EIS2K1.main hL a

end S_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
end P2MW
export P2MW.S_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty (solution)
