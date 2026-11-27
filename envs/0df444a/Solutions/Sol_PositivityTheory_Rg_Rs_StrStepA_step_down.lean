-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.StrStepA.step_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:19:38.579485+00:00
-- url     : https://prove2.me/submissions/2f940d1e-ed00-4fb2-a3dd-8508319fe80b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_SdNormCpow
import Theorems.Thm_PositivityTheory_Rg_Rs_StrStepA_sd_norm_cpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.StrStepA
namespace PositivityTheory.Rg.Rs.StrStepA
theorem _root_.solution (q : ℕ) (hq : 1 < q) (B₀ : Multiset ℂ)
    (hB : ∀ β ∈ B₀, (q : ℝ) ^ (-(1 / 2) : ℝ) < ‖β‖ ∧ ‖β‖ < (q : ℝ) ^ (1 / 2 : ℝ)) {α : ℂ} (hα : α ∈ B₀)
    (S : Set ℝ) (hint : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, x - y = n) (M : Multiset ℂ)
    (hM : ∀ z, z ∈ M ↔ ∃ x ∈ S, ∃ β ∈ B₀, z = β * (q : ℂ) ^ (-(x : ℂ)))
    (hgap : ∀ z : ℂ, ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) → M.count z ≤ M.count ((q : ℂ) * z))
    {u : ℝ} (hu : u ∈ S) (hu1 : 1 ≤ u) : u - 1 ∈ S := by
  have hQ : (1 : ℝ) < q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  set z : ℂ := α * (q : ℂ) ^ (-(u : ℂ)) with hz
  have hzM : z ∈ M := (hM z).2 ⟨u, hu, α, hα, rfl⟩
  have hnz : ‖z‖ = ‖α‖ * (q : ℝ) ^ (-u) := by rw [hz, norm_mul, sd_norm_cpow q hq]
  have hsmall : ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [hnz]
    have h1 : ‖α‖ * (q : ℝ) ^ (-u) < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-u) :=
      mul_lt_mul_of_pos_right (hB α hα).2 (Real.rpow_pos_of_pos hQ0 _)
    have h2 : (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-u) = (q : ℝ) ^ (1 / 2 - u) := by
      rw [← Real.rpow_add hQ0]; ring_nf
    have h3 : (q : ℝ) ^ (1 / 2 - u) ≤ (q : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hQ.le (by linarith)
    linarith
  have hc1 : 0 < M.count z := Multiset.count_pos.2 hzM
  have hc2 : 0 < M.count ((q : ℂ) * z) := lt_of_lt_of_le hc1 (hgap z hsmall)
  obtain ⟨x, hx, β, hβ, e⟩ := (hM _).1 (Multiset.count_pos.1 hc2)
  have en : (q : ℝ) * (‖α‖ * (q : ℝ) ^ (-u)) = ‖β‖ * (q : ℝ) ^ (-x) := by
    have h := congrArg norm e
    rw [norm_mul, hnz, norm_mul, sd_norm_cpow q hq, Complex.norm_natCast] at h
    exact h
  have hβn : ‖β‖ = ‖α‖ * (q : ℝ) ^ (1 - u + x) := by
    have e1 : (q : ℝ) ^ (1 - u + x) = q * (q : ℝ) ^ (-u) * (q : ℝ) ^ x := by
      rw [Real.rpow_add hQ0, Real.rpow_sub hQ0, Real.rpow_one, Real.rpow_neg hQ0.le]
      field_simp
    have hxx : (q : ℝ) ^ (-x) * (q : ℝ) ^ x = 1 := by rw [← Real.rpow_add hQ0]; simp
    calc ‖β‖ = ‖β‖ * (q : ℝ) ^ (-x) * (q : ℝ) ^ x := by rw [mul_assoc, hxx, mul_one]
      _ = q * (‖α‖ * (q : ℝ) ^ (-u)) * (q : ℝ) ^ x := by rw [en]
      _ = ‖α‖ * (q : ℝ) ^ (1 - u + x) := by rw [e1]; ring
  obtain ⟨n, hn⟩ := hint x hx u hu
  have hk : 1 - u + x = ((n + 1 : ℤ) : ℝ) := by push_cast; linarith
  rw [hk, Real.rpow_intCast] at hβn
  obtain ⟨hb1, hb2⟩ := hB β hβ
  obtain ⟨ha1, ha2⟩ := hB α hα
  have hpos : (0 : ℝ) < (q : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hQ0 _
  have hhalf : (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) = (q : ℝ) ^ (1 / 2 : ℝ) := by
    have h := (Real.rpow_add hQ0 (-(1 / 2) : ℝ) 1).symm
    rw [Real.rpow_one] at h
    rw [h]; norm_num
  rcases lt_trichotomy (n + 1) 0 with hneg | hzero | hposn
  ·
    exfalso
    have hle : (q : ℝ) ^ (n + 1) ≤ (q : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hQ.le (by omega)
    have hzp : (0 : ℝ) < (q : ℝ) ^ (n + 1) := zpow_pos hQ0 _
    have : ‖β‖ < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (-1 : ℤ) := by
      rw [hβn]
      calc ‖α‖ * (q : ℝ) ^ (n + 1) < (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (n + 1) := mul_lt_mul_of_pos_right ha2 hzp
        _ ≤ _ := mul_le_mul_of_nonneg_left hle (Real.rpow_pos_of_pos hQ0 _).le
    rw [← hhalf, zpow_neg_one, mul_assoc, mul_inv_cancel₀ hQ0.ne', mul_one] at this
    linarith
  · have hx' : x = u - 1 := by
      have : (n : ℝ) = -1 := by exact_mod_cast (by omega : n = -1)
      linarith
    rw [← hx']; exact hx
  · exfalso
    have hle : (q : ℝ) ^ (1 : ℤ) ≤ (q : ℝ) ^ (n + 1) := zpow_le_zpow_right₀ hQ.le (by omega)
    have : (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (1 : ℤ) < ‖β‖ := by
      rw [hβn]
      calc (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (1 : ℤ) ≤ (q : ℝ) ^ (-(1 / 2) : ℝ) * (q : ℝ) ^ (n + 1) :=
            mul_le_mul_of_nonneg_left hle hpos.le
        _ < ‖α‖ * (q : ℝ) ^ (n + 1) := mul_lt_mul_of_pos_right ha1 (zpow_pos hQ0 _)
    rw [zpow_one, hhalf] at this
    linarith
end PositivityTheory.Rg.Rs.StrStepA
