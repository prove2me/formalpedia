-- Prove2me | solution 1 for SmoothedSimplex.Shadow.shadow_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T16:49:36.805174+00:00
-- url     : https://prove2.me/submissions/511bd700-9a0e-46d7-ab47-940dd75e4070

import Mathlib
import Definitions.Def_SmoothedSimplex_Shadow_gaussian
import Definitions.Def_SmoothedSimplex_Shadow_shadow
import Definitions.Def_SmoothedSimplex_Shadow_shadowBound
import Theorems.Thm_FriendlyShadow_Gaussian_theorem_13
import Theorems.Thm_SmoothedSimplex_Shadow_shadow_card_ae_le_edgeCount

set_option autoImplicit false

namespace E0Red

/-- The Dadush–Huiberts Gaussian bound (theorem_13) is below the Spielman–Teng bound 𝒟(n,d,σ). -/
lemma arith {d n : ℕ} (hd : 3 ≤ d) (hn : d < n) (σ : ℝ) (hσ : 0 < σ) :
    3 + 128 * Real.pi * Real.exp 2 * (d : ℝ) ^ 2 * Real.sqrt (Real.log n) /
        σ ^ 2 * (1 + 4 * σ * Real.sqrt (d * Real.log n)) *
        (1 + 16 * σ * Real.sqrt (Real.log n)) ≤ SmoothedSimplex.Shadow.shadowBound n d σ := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
  set L := Real.log n with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  set A := Real.sqrt (d * L) with hAdef
  set B := Real.sqrt L with hBdef
  have hB1 : 1 ≤ B := by
    rw [hBdef, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hL1
  have hBA : B ≤ A := Real.sqrt_le_sqrt (by nlinarith)
  have hA1 : 1 ≤ A := hB1.trans hBA
  have hApos : 0 < A := by linarith
  set m := min σ (1 / (3 * A)) with hmdef
  have hm_pos : 0 < m := lt_min hσ (by positivity)
  set S := 1 / m with hSdef
  have hSpos : 0 < S := by positivity
  have hSσ : 1 / σ ≤ S := one_div_le_one_div_of_le hm_pos (min_le_left _ _)
  have hSA : 3 * A ≤ S := by
    have h1 : m ≤ 1 / (3 * A) := min_le_right _ _
    rw [hSdef, le_div_iff₀ hm_pos]
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hS3 : 3 ≤ S := by linarith
  have hC : 128 * Real.pi * Real.exp 2 ≤ 3000 := by
    have hpi := Real.pi_lt_d2
    have he := Real.exp_one_lt_d9
    have he0 := Real.exp_pos 1
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [h2]
    have : Real.exp 1 * Real.exp 1 ≤ 7.39 := by nlinarith
    nlinarith [Real.pi_pos]
  have hCpos : 0 < 128 * Real.pi * Real.exp 2 := by positivity
  set u := 1 / σ with hudef
  have hupos : 0 < u := by positivity
  have hEq : 128 * Real.pi * Real.exp 2 * (d : ℝ) ^ 2 * B / σ ^ 2 * (1 + 4 * σ * A) *
      (1 + 16 * σ * B) = (128 * Real.pi * Real.exp 2) * ((d : ℝ) ^ 2 * B * (u + 4 * A) *
        (u + 16 * B)) := by
    rw [hudef]; field_simp
  have hf1 : u + 4 * A ≤ 7 / 3 * S := by linarith
  have hf2 : u + 16 * B ≤ 19 / 3 * S := by linarith
  have hBS : B ≤ S / 3 := by linarith
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := by positivity
  have hprod : (d : ℝ) ^ 2 * B * (u + 4 * A) * (u + 16 * B) ≤ 5 * ((d : ℝ) ^ 2 * S ^ 3) := by
    have h1 : B * (u + 4 * A) ≤ (S / 3) * (7 / 3 * S) :=
      mul_le_mul hBS hf1 (by linarith) (by linarith)
    have h2 : B * (u + 4 * A) * (u + 16 * B) ≤ (S / 3) * (7 / 3 * S) * (19 / 3 * S) :=
      mul_le_mul h1 hf2 (by linarith) (by positivity)
    have h3 : (S / 3) * (7 / 3 * S) * (19 / 3 * S) ≤ 5 * S ^ 3 := by
      have e : (S / 3) * (7 / 3 * S) * (19 / 3 * S) = 133 / 27 * S ^ 3 := by ring
      have : 0 < S ^ 3 := pow_pos hSpos 3
      rw [e]; linarith
    calc (d : ℝ) ^ 2 * B * (u + 4 * A) * (u + 16 * B)
        = (d : ℝ) ^ 2 * (B * (u + 4 * A) * (u + 16 * B)) := by ring
      _ ≤ (d : ℝ) ^ 2 * (5 * S ^ 3) := mul_le_mul_of_nonneg_left (h2.trans h3) hd2
      _ = 5 * ((d : ℝ) ^ 2 * S ^ 3) := by ring
  have hS3' : (1 : ℝ) ≤ S ^ 3 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ S)
  have hP1 : 1 ≤ (d : ℝ) ^ 2 * S ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith : (1 : ℝ) ≤ d)) hS3'
  have hPle : (d : ℝ) ^ 2 * S ^ 3 ≤ (n : ℝ) * (d : ℝ) ^ 3 * S ^ 6 := by
    have hnd : (1 : ℝ) ≤ (n : ℝ) * (d : ℝ) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have hP0 : (0 : ℝ) ≤ (d : ℝ) ^ 2 * S ^ 3 := by positivity
    calc (d : ℝ) ^ 2 * S ^ 3 = 1 * 1 * ((d : ℝ) ^ 2 * S ^ 3) := by ring
      _ ≤ ((n : ℝ) * (d : ℝ)) * S ^ 3 * ((d : ℝ) ^ 2 * S ^ 3) := by
          apply mul_le_mul_of_nonneg_right _ hP0
          exact mul_le_mul hnd hS3' (by norm_num) (by linarith)
      _ = (n : ℝ) * (d : ℝ) ^ 3 * S ^ 6 := by ring
  have hRHS : SmoothedSimplex.Shadow.shadowBound n d σ = 58888678 * ((n : ℝ) * (d : ℝ) ^ 3 * S ^ 6) := by
    unfold SmoothedSimplex.Shadow.shadowBound
    rw [← hLdef, ← hAdef, ← hmdef, hSdef]
    field_simp
  rw [hRHS, hEq]
  have hT : (128 * Real.pi * Real.exp 2) * ((d : ℝ) ^ 2 * B * (u + 4 * A) * (u + 16 * B)) ≤
      3000 * (5 * ((d : ℝ) ^ 2 * S ^ 3)) :=
    mul_le_mul hC hprod (by positivity) (by norm_num)
  linarith

end E0Red

open MeasureTheory ProbabilityTheory SmoothedSimplex.Shadow in
theorem solution {d n : ℕ} (hd : 3 ≤ d) (hn : d < n)
    (z t : EuclideanSpace ℝ (Fin d)) (hzt : LinearIndependent ℝ ![z, t])
    (σ : ℝ) (hσ : 0 < σ)
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (habar : ∀ i, ‖abar i‖ ≤ 1) :
    let μ : Measure (Fin n → EuclideanSpace ℝ (Fin d)) := Measure.pi (fun i => gaussian (abar i) σ)
    AEMeasurable (fun a => ((shadow t z a).card : ENNReal)) μ ∧
      ∫⁻ a, ((shadow t z a).card : ENNReal) ∂μ ≤ ENNReal.ofReal (shadowBound n d σ) := by
  intro μ
  obtain ⟨hmeas, hae⟩ :=
    SmoothedSimplex.Shadow.shadow_card_ae_le_edgeCount hd hn.le z t hzt σ hσ abar
  have hW : Module.finrank ℝ (Submodule.span ℝ {t, z}) = 2 := by
    have h := finrank_span_eq_card hzt
    have hr : Set.range ![z, t] = {t, z} := by
      ext x; simp [eq_comm, or_comm]
    rw [hr] at h; simpa using h
  have h13 := FriendlyShadow.Gaussian.theorem_13 hd hn.le (Submodule.span ℝ {t, z}) hW abar
    habar σ hσ
  refine ⟨hmeas, ?_⟩
  calc ∫⁻ a, ((shadow t z a).card : ENNReal) ∂μ
      ≤ ∫⁻ a, (FriendlyShadow.Gaussian.edgeCount
          (FriendlyShadow.Gaussian.polygon (Submodule.span ℝ {t, z}) a) : ENNReal) ∂μ :=
        lintegral_mono_ae (hae.mono fun a ha => by exact_mod_cast ha)
    _ ≤ _ := h13.2
    _ ≤ ENNReal.ofReal (shadowBound n d σ) := ENNReal.ofReal_le_ofReal (E0Red.arith hd hn σ hσ)
