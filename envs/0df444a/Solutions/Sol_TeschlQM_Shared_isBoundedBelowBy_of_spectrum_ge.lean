-- Prove2me | solution 1 for TeschlQM.Shared.isBoundedBelowBy_of_spectrum_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T09:45:23.343096+00:00
-- url     : https://prove2.me/submissions/5e1fb0cf-7b53-4f60-a54f-516ca9390f26

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Shared_essentialSpectrum
import Definitions.Def_TeschlQM_Shared_IsBoundedBelowBy
import Definitions.Def_TeschlQM_Shared_IsSymmetric

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate

namespace HVZD3a

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma inner_self_c (x : H) : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re, ← RCLike.re_to_complex]; exact inner_self_eq_norm_sq (𝕜 := ℂ) x
  · rw [Complex.ofReal_im, ← RCLike.im_to_complex]; exact inner_self_im (𝕜 := ℂ) x

/-- the infimum `m` of the numerical range of a symmetric operator bounded below lies in the spectrum -/
theorem inf_mem_spectrum (A : H →ₗ.[ℂ] H)
    (hA : ∀ φ ψ : A.domain, ⟪A φ, (ψ : H)⟫_ℂ = ⟪(φ : H), A ψ⟫_ℂ)
    (S : Set ℝ) (hS : S = {r | ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧
      r = (⟪(ψ : H), A ψ⟫_ℂ).re / ‖(ψ : H)‖ ^ 2})
    (hSne : S.Nonempty) (m : ℝ) (hm_def : m = sInf S)
    (hm : ∀ ψ : A.domain, m * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re) :
    (m : ℂ) ∈ TeschlQM.Shared.spectrum A := by
  subst hS
  -- m is in the spectrum
  rintro ⟨R, hR⟩
  have herm : ∀ x y : H, ⟪x, R y⟫_ℂ = ⟪R x, y⟫_ℂ := by
    intro x y
    obtain ⟨hx, ex⟩ := hR.1 x
    obtain ⟨hy, ey⟩ := hR.1 y
    have hs : ⟪A ⟨R x, hx⟩, R y⟫_ℂ = ⟪R x, A ⟨R y, hy⟩⟫_ℂ := hA ⟨R x, hx⟩ ⟨R y, hy⟩
    calc ⟪x, R y⟫_ℂ = ⟪A ⟨R x, hx⟩ - (m : ℂ) • R x, R y⟫_ℂ := by rw [ex]
      _ = ⟪A ⟨R x, hx⟩, R y⟫_ℂ - (m : ℂ) * ⟪R x, R y⟫_ℂ := by
        rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal]
      _ = ⟪R x, A ⟨R y, hy⟩⟫_ℂ - (m : ℂ) * ⟪R x, R y⟫_ℂ := by rw [hs]
      _ = ⟪R x, A ⟨R y, hy⟩ - (m : ℂ) • R y⟫_ℂ := by rw [inner_sub_right, inner_smul_right]
      _ = ⟪R x, y⟫_ℂ := by rw [ey]
  have hpos : ∀ y : H, 0 ≤ (⟪y, R y⟫_ℂ).re := by
    intro y
    obtain ⟨hy, ey⟩ := hR.1 y
    have h1 := hm ⟨R y, hy⟩
    have hs : ⟪A ⟨R y, hy⟩, R y⟫_ℂ = ⟪R y, A ⟨R y, hy⟩⟫_ℂ := hA ⟨R y, hy⟩ ⟨R y, hy⟩
    have : ⟪y, R y⟫_ℂ = ⟪R y, A ⟨R y, hy⟩⟫_ℂ - (m : ℂ) * ((‖R y‖ ^ 2 : ℝ) : ℂ) := by
      calc ⟪y, R y⟫_ℂ = ⟪A ⟨R y, hy⟩ - (m : ℂ) • R y, R y⟫_ℂ := by rw [ey]
        _ = _ := by
          rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, hs, inner_self_c]
    rw [this, Complex.sub_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    have h1' : m * ‖R y‖ ^ 2 ≤ (⟪R y, A ⟨R y, hy⟩⟫_ℂ).re := h1
    linarith
  let c : PreInnerProductSpace.Core ℂ H :=
    { inner := fun x y => ⟪x, R y⟫_ℂ
      conj_inner_symm := fun x y => by
        show conj ⟪y, R x⟫_ℂ = ⟪x, R y⟫_ℂ
        rw [inner_conj_symm, herm]
      re_inner_nonneg := fun x => hpos x
      add_left := fun x y z => inner_add_left _ _ _
      smul_left := fun x y r => inner_smul_left _ _ _ }
  -- pick ψ with small Rayleigh quotient
  have hε : 0 < 1 / (‖R‖ + 1) := by positivity
  obtain ⟨r, ⟨ψ, hψ0, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hSne (by rw [← hm_def]; exact lt_add_of_pos_right m hε)
  have hn : 0 < ‖(ψ : H)‖ := norm_pos_iff.mpr hψ0
  have hq : (⟪(ψ : H), A ψ⟫_ℂ).re < (m + 1 / (‖R‖ + 1)) * ‖(ψ : H)‖ ^ 2 := by
    rwa [div_lt_iff₀ (by positivity)] at hlt
  set χ := A ψ - (m : ℂ) • (ψ : H) with hχ
  have hRχ : R χ = ψ := hR.2 ψ
  have hcs := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ H _ _ _ c (R χ) χ
  change ‖⟪R χ, R χ⟫_ℂ‖ * ‖⟪χ, R (R χ)⟫_ℂ‖ ≤ (⟪R χ, R (R χ)⟫_ℂ).re * (⟪χ, R χ⟫_ℂ).re at hcs
  rw [herm χ (R χ), hRχ, inner_self_c, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)] at hcs
  have hA1 : (⟪χ, (ψ : H)⟫_ℂ).re = (⟪(ψ : H), A ψ⟫_ℂ).re - m * ‖(ψ : H)‖ ^ 2 := by
    have hs : ⟪A ψ, (ψ : H)⟫_ℂ = ⟪(ψ : H), A ψ⟫_ℂ := hA ψ ψ
    rw [hχ, inner_sub_left, inner_smul_left, Complex.conj_ofReal, hs, inner_self_c,
      Complex.sub_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hRR : (⟪(ψ : H), R ψ⟫_ℂ).re ≤ ‖R‖ * ‖(ψ : H)‖ ^ 2 := by
    calc (⟪(ψ : H), R ψ⟫_ℂ).re ≤ ‖⟪(ψ : H), R ψ⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖(ψ : H)‖ * ‖R ψ‖ := norm_inner_le_norm _ _
      _ ≤ ‖(ψ : H)‖ * (‖R‖ * ‖(ψ : H)‖) := by gcongr; exact R.le_opNorm _
      _ = ‖R‖ * ‖(ψ : H)‖ ^ 2 := by ring
  rw [hA1] at hcs
  -- hcs : n^2 * n^2 ≤ re⟪ψ,Rψ⟫ * (q - m n^2)
  set n2 := ‖(ψ : H)‖ ^ 2
  have hn2 : 0 < n2 := by positivity
  set D := (⟪(ψ : H), A ψ⟫_ℂ).re - m * n2
  have hD0 : 0 ≤ D := by have := hm ψ; simp only [D]; linarith
  have hD1 : D < 1 / (‖R‖ + 1) * n2 := by simp only [D]; nlinarith
  have hRn : 0 ≤ ‖R‖ := norm_nonneg _
  have key : n2 * n2 ≤ ‖R‖ * n2 * (1 / (‖R‖ + 1) * n2) := by
    calc n2 * n2 ≤ (⟪(ψ : H), R ψ⟫_ℂ).re * D := hcs
      _ ≤ (‖R‖ * n2) * D := by
        apply mul_le_mul_of_nonneg_right hRR hD0
      _ ≤ ‖R‖ * n2 * (1 / (‖R‖ + 1) * n2) := by
        apply mul_le_mul_of_nonneg_left hD1.le; positivity
  have : 1 ≤ ‖R‖ * (1 / (‖R‖ + 1)) := by
    have h' : n2 * n2 * 1 ≤ n2 * n2 * (‖R‖ * (1 / (‖R‖ + 1))) := by nlinarith
    exact le_of_mul_le_mul_left h' (by positivity)
  rw [mul_one_div, le_div_iff₀ (by positivity)] at this
  linarith

end HVZD3a

theorem solution {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : TeschlQM.Shared.IsSymmetric A)
    (γ : ℝ) (hγ : TeschlQM.Shared.IsBoundedBelowBy A γ) (t : ℝ)
    (ht : (t : ℂ) ∈ TeschlQM.Shared.resolventSet A) (lam : ℝ)
    (hlam : ∀ z ∈ TeschlQM.Shared.spectrum A, z.im = 0 ∧ lam ≤ z.re) :
    TeschlQM.Shared.IsBoundedBelowBy A lam := by
  have hA' : ∀ φ ψ : A.domain, ⟪A φ, (ψ : H)⟫_ℂ = ⟪(φ : H), A ψ⟫_ℂ :=
    fun φ ψ => (hA.2 φ ψ).symm
  by_cases hex : ∃ ψ : A.domain, (ψ : H) ≠ 0
  swap
  · intro ψ
    push Not at hex
    rw [hex ψ, norm_zero, inner_zero_left]; simp
  set S : Set ℝ := {r | ∃ ψ : A.domain, (ψ : H) ≠ 0 ∧
    r = (⟪(ψ : H), A ψ⟫_ℂ).re / ‖(ψ : H)‖ ^ 2} with hS
  have hbdd : BddBelow S := by
    refine ⟨γ, ?_⟩
    rintro r ⟨ψ, hψ, rfl⟩
    have : 0 < ‖(ψ : H)‖ := norm_pos_iff.mpr hψ
    rw [le_div_iff₀ (by positivity)]; exact hγ ψ
  have hSne : S.Nonempty := by
    obtain ⟨ψ, hψ⟩ := hex
    exact ⟨_, ψ, hψ, rfl⟩
  have hm : ∀ ψ : A.domain, sInf S * ‖(ψ : H)‖ ^ 2 ≤ (⟪(ψ : H), A ψ⟫_ℂ).re := by
    intro ψ
    rcases eq_or_ne (ψ : H) 0 with h0 | h0
    · rw [h0, norm_zero, inner_zero_left]; simp
    have hn : 0 < ‖(ψ : H)‖ := norm_pos_iff.mpr h0
    have := csInf_le hbdd ⟨ψ, h0, rfl⟩
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  have hmem := HVZD3a.inf_mem_spectrum A hA' S hS hSne (sInf S) rfl hm
  have hle : lam ≤ sInf S := by
    have := (hlam _ hmem).2
    rwa [Complex.ofReal_re] at this
  intro ψ
  have h1 := hm ψ
  have h2 : 0 ≤ ‖(ψ : H)‖ ^ 2 := by positivity
  nlinarith
