-- Prove2me | solution 1 for PolyhedralSOC.UpperBound.planar_approx_extend
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:38:41.774979+00:00
-- url     : https://prove2.me/submissions/730aacfd-abb0-4e9e-bd04-9dfe1c79d12d

import Mathlib
import Definitions.Def_PolyhedralSOC_UpperBound_System8

namespace PolyhedralSOC.UpperBound

/-- The angles `φ_j`: `φ_0` given, `φ_{j+1} = |φ_j - π/2^{j+2}|`. -/
noncomputable def aux_pae_phi (φ0 : ℝ) : ℕ → ℝ
  | 0 => φ0
  | (j+1) => |aux_pae_phi φ0 j - Real.pi / 2 ^ (j + 2)|

lemma aux_pae_phi_bound (φ0 : ℝ) (h0 : 0 ≤ φ0) (h1 : φ0 ≤ Real.pi / 2) :
    ∀ j, 0 ≤ aux_pae_phi φ0 j ∧ aux_pae_phi φ0 j ≤ Real.pi / 2 ^ (j + 1) := by
  intro j
  induction j with
  | zero => simpa [aux_pae_phi] using ⟨h0, h1⟩
  | succ k ih =>
    refine ⟨abs_nonneg _, ?_⟩
    show |aux_pae_phi φ0 k - Real.pi / 2 ^ (k + 2)| ≤ Real.pi / 2 ^ (k + 2)
    have e : Real.pi / 2 ^ (k + 1) = 2 * (Real.pi / 2 ^ (k + 2)) := by
      rw [pow_succ 2 (k + 1)]
      field_simp
    have hp : 0 ≤ Real.pi / 2 ^ (k + 2) := by positivity
    rw [abs_sub_le_iff]
    constructor <;> linarith [ih.1, ih.2]

lemma aux_pae_abs_sin (a : ℝ) (ha : |a| ≤ Real.pi) : |Real.sin a| = Real.sin |a| := by
  have h0 : 0 ≤ Real.sin |a| := Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg a) ha
  rcases abs_cases a with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h] at h0 ⊢
    exact abs_of_nonneg h0
  · rw [h] at h0 ⊢
    rw [Real.sin_neg] at h0 ⊢
    exact abs_of_nonpos (by linarith)

end PolyhedralSOC.UpperBound

open PolyhedralSOC.UpperBound

theorem solution (ν : ℕ) (hν : 1 ≤ ν) (x₁ x₂ x₃ : ℝ)
    (hx : Real.sqrt (x₁ ^ 2 + x₂ ^ 2) ≤ x₃) :
    ∃ ξ η : ℕ → ℝ, System8 ν x₁ x₂ x₃ ξ η := by
  set z : ℂ := ⟨|x₁|, |x₂|⟩ with hz
  set r := ‖z‖ with hrdef
  have hr : r = Real.sqrt (x₁ ^ 2 + x₂ ^ 2) := by
    rw [hrdef, Complex.norm_def, hz, Complex.normSq_mk]
    congr 1
    rw [abs_mul_abs_self x₁, abs_mul_abs_self x₂]
    ring
  have hc : r * Real.cos (Complex.arg z) = |x₁| := Complex.norm_mul_cos_arg z
  have hs : r * Real.sin (Complex.arg z) = |x₂| := Complex.norm_mul_sin_arg z
  have ha0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr (abs_nonneg _)
  have ha1 : Complex.arg z ≤ Real.pi / 2 :=
    Complex.arg_le_pi_div_two_iff.mpr (Or.inl (abs_nonneg _))
  have hb := aux_pae_phi_bound _ ha0 ha1
  have hr0 : 0 ≤ r := norm_nonneg _
  refine ⟨fun j => r * Real.cos (aux_pae_phi (Complex.arg z) j),
    fun j => r * Real.sin (aux_pae_phi (Complex.arg z) j), ?_, ?_, ?_⟩
  · simp only [aux_pae_phi]
    exact ⟨hc.ge, hs.ge⟩
  · intro j hj1 hjν
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hφ : aux_pae_phi (Complex.arg z) (k + 1)
        = |aux_pae_phi (Complex.arg z) k - Real.pi / 2 ^ (k + 1 + 1)| := rfl
    rw [hφ]
    set φ := aux_pae_phi (Complex.arg z) k
    set θ := Real.pi / 2 ^ (k + 1 + 1)
    have hbd : |φ - θ| ≤ Real.pi := by
      have h1 := (hb (k + 1)).2
      rw [hφ] at h1
      have h2 : Real.pi / 2 ^ (k + 1 + 1) ≤ Real.pi :=
        div_le_self Real.pi_pos.le (one_le_pow₀ (by norm_num))
      exact h1.trans h2
    constructor
    · rw [Real.cos_abs, Real.cos_sub]
      ring
    · have e : -Real.sin θ * (r * Real.cos φ) + Real.cos θ * (r * Real.sin φ)
          = r * Real.sin (φ - θ) := by
        rw [Real.sin_sub]; ring
      rw [e, abs_mul, abs_of_nonneg hr0, aux_pae_abs_sin _ hbd]
  · have hbν := hb ν
    set φ := aux_pae_phi (Complex.arg z) ν
    set θ := Real.pi / 2 ^ (ν + 1)
    have hθ : θ < Real.pi / 2 := by
      have h4 : (2 : ℝ) ^ 1 < 2 ^ (ν + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by simpa using h4)
    have hcos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    constructor
    · show r * Real.cos φ ≤ x₃
      calc r * Real.cos φ ≤ r * 1 := mul_le_mul_of_nonneg_left (Real.cos_le_one _) hr0
        _ = r := mul_one r
        _ ≤ x₃ := hr ▸ hx
    · show r * Real.sin φ ≤ Real.tan θ * (r * Real.cos φ)
      have htan : Real.tan φ ≤ Real.tan θ :=
        Real.strictMonoOn_tan.monotoneOn ⟨by linarith [Real.pi_pos], by linarith⟩
          ⟨by linarith [Real.pi_pos], hθ⟩ hbν.2
      have hsin : Real.sin φ = Real.tan φ * Real.cos φ := by
        rw [Real.tan_eq_sin_div_cos]; field_simp
      rw [hsin]
      have := mul_le_mul_of_nonneg_right htan (mul_nonneg hr0 hcos.le)
      nlinarith [this]
