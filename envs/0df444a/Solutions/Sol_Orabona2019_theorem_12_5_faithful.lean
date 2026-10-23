-- Prove2me | solution 1 for Orabona2019.theorem_12_5_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T04:33:57.281571+00:00
-- url     : https://prove2.me/submissions/5628a282-adf9-4b38-8500-a1c1a9afd481

import Mathlib
import Definitions.Def_ModernOnlineLearning_OGD_Defs
import Definitions.Def_ModernOnlineLearning_Reductions_Setting

open ModernOnlineLearning.Reductions

namespace OR86

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A subgradient of an `L`-Lipschitz function has dual norm at most `L`. -/
lemma sub_norm_le {f : E → ℝ} {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ a b, f a - f b ≤ L * ‖a - b‖)
    {y : E} {g' : E →L[ℝ] ℝ} (hg : IsSubgradient f y g') : ‖g'‖ ≤ L := by
  refine ContinuousLinearMap.opNorm_le_bound _ hL0 (fun v => ?_)
  have h1 := hg (y + v)
  have h2 := hg (y - v)
  have h3 := hL (y + v) y
  have h4 := hL (y - v) y
  simp only [add_sub_cancel_left, sub_sub_cancel_left, map_neg] at h1 h2 h3 h4
  rw [norm_neg] at h4
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

lemma dist_lip (V : Set E) (a b : E) : distance V a - distance V b ≤ 1 * ‖a - b‖ := by
  unfold distance
  have := Metric.infDist_le_infDist_add_dist (x := a) (y := b) (s := V)
  rw [dist_eq_norm] at this; linarith

lemma g_lip (g : E →L[ℝ] ℝ) (a b : E) : g a - g b ≤ ‖g‖ * ‖a - b‖ := by
  rw [← map_sub]; exact (le_abs_self _).trans (by simpa using g.le_opNorm (a - b))

lemma q_lip (q : E →L[ℝ] ℝ) (hq : ‖q‖ ≤ 1) (a b : E) : q a - q b ≤ 1 * ‖a - b‖ := by
  refine (g_lip q a b).trans ?_
  exact mul_le_mul_of_nonneg_right hq (norm_nonneg _)

lemma c_le (g : E →L[ℝ] ℝ) (x z : E) : |g ((‖x - z‖)⁻¹ • (x - z))| ≤ ‖g‖ := by
  have h1 := g.le_opNorm ((‖x - z‖)⁻¹ • (x - z))
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  by_cases h : ‖x - z‖ = 0
  · simp [h]
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h, mul_one]

lemma lip_add {f₁ f₂ : E → ℝ} {L₁ L₂ c : ℝ}
    (h₁ : ∀ a b, f₁ a - f₁ b ≤ L₁ * ‖a - b‖) (h₂ : ∀ a b, f₂ a - f₂ b ≤ L₂ * ‖a - b‖) (hL₂ : 0 ≤ L₂) :
    ∀ a b, (f₁ a + c * f₂ a) - (f₁ b + c * f₂ b) ≤ (L₁ + |c| * L₂) * ‖a - b‖ := by
  intro a b
  have h2a := h₂ a b
  have h2b := h₂ b a
  rw [norm_sub_rev] at h2b
  have : c * (f₂ a - f₂ b) ≤ |c| * (L₂ * ‖a - b‖) := by
    calc c * (f₂ a - f₂ b) ≤ |c * (f₂ a - f₂ b)| := le_abs_self _
      _ = |c| * |f₂ a - f₂ b| := abs_mul _ _
      _ ≤ |c| * (L₂ * ‖a - b‖) := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, h2a⟩) (abs_nonneg c)
  have := h₁ a b
  nlinarith

end OR86

open OR86 in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V W : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) (hVW : V ⊆ W)
    (loss : ℕ → E → ℝ) (z x : ℕ → E) (g q : ℕ → E →L[ℝ] ℝ)
    (T : ℕ) (hT : 1 ≤ T) (hRun : IsProjectedRun V W loss z x g q T)
    (u : E) (hu : u ∈ V) :
    (∀ k : Fin 4, ModernOnlineLearning.OGD.regret loss x u T ≤ surrogateRegret k V z x g q u T) ∧
    (∀ k : Fin 4, ∀ t ∈ Finset.Icc 1 T, ∀ y ∈ W, ∀ g' : E →L[ℝ] ℝ,
      IsSubgradient (fun w => surrogate k V (g t) (q t) (x t) (z t) w) y g' →
        ‖g'‖ ≤ 2 * ‖g t‖) := by
  have hdu : distance V u = 0 := Metric.infDist_zero_of_mem hu
  have hqn : ∀ t ∈ Finset.Icc 1 T, ‖q t‖ ≤ 1 := fun t ht =>
    sub_norm_le zero_le_one (dist_lip V) (hRun t ht).2.2.2
  constructor
  · intro k
    unfold ModernOnlineLearning.OGD.regret surrogateRegret
    apply Finset.sum_le_sum
    intro t ht
    obtain ⟨_, ⟨hxV, hproj⟩, hsub, hqs⟩ := hRun t ht
    have h1 := hsub u hu
    have h2 := hqs u
    rw [hdu] at h2
    have hgx : g t (x t) - g t (z t) ≤ ‖g t‖ * ‖x t - z t‖ := g_lip (g t) _ _
    rw [norm_sub_rev] at hgx
    have hl : loss t (x t) - loss t u ≤ g t (x t) - g t u := by
      rw [map_sub] at h1; linarith
    simp only [map_sub] at h2
    have hq : ‖z t - x t‖ ≤ q t (z t) - q t u := by rw [hproj]; linarith
    have hgn : 0 ≤ ‖g t‖ := norm_nonneg _
    fin_cases k <;> simp only [surrogate] <;> simp
    · rw [hdu, ← hproj]; linarith
    · nlinarith [mul_le_mul_of_nonneg_left hq hgn]
    · split_ifs with hc
      · linarith
      · have hne : ‖x t - z t‖ ≠ 0 := by
          intro h0; rw [norm_eq_zero, sub_eq_zero] at h0; rw [h0] at hc; exact hc le_rfl
        rw [hdu, ← hproj]
        have e : ‖x t - z t‖⁻¹ * (g t (x t) - g t (z t)) * ‖z t - x t‖ = g t (x t) - g t (z t) := by
          rw [norm_sub_rev (z t) (x t)]; field_simp
        linarith
    · split_ifs with hc
      · linarith
      · have hne : 0 < ‖x t - z t‖ := by
          rcases (norm_nonneg (x t - z t)).lt_or_eq with h | h
          · exact h
          · rw [eq_comm, norm_eq_zero, sub_eq_zero] at h; rw [h] at hc; exact absurd le_rfl hc
        have hcpos : 0 < ‖x t - z t‖⁻¹ * (g t (x t) - g t (z t)) :=
          mul_pos (inv_pos.mpr hne) (by linarith [lt_of_not_ge hc])
        have e : ‖x t - z t‖⁻¹ * (g t (x t) - g t (z t)) * ‖z t - x t‖ = g t (x t) - g t (z t) := by
          rw [norm_sub_rev (z t) (x t)]; field_simp
        nlinarith [mul_le_mul_of_nonneg_left hq hcpos.le]
  · intro k t ht y _ g' hg'
    have hgn : 0 ≤ ‖g t‖ := norm_nonneg _
    have hc := c_le (g t) (x t) (z t)
    have hq1 := hqn t ht
    set c := (g t) ((‖x t - z t‖)⁻¹ • (x t - z t))
    fin_cases k
    · have hL := lip_add (c := ‖g t‖) (g_lip (g t)) (dist_lip V) zero_le_one
      refine (sub_norm_le (y := y) (by positivity) hL ?_).trans ?_
      · intro w; have := hg' w; simpa [surrogate] using this
      · rw [abs_of_nonneg hgn]; linarith
    · have hL := lip_add (c := ‖g t‖) (g_lip (g t)) (q_lip (q t) hq1) zero_le_one
      refine (sub_norm_le (y := y) (by positivity) hL ?_).trans ?_
      · intro w; have := hg' w; simpa [surrogate] using this
      · rw [abs_of_nonneg hgn]; linarith
    · by_cases hcz : g t (x t - z t) ≤ 0
      · have hcz' : (g t) (x t) ≤ (g t) (z t) := by rw [map_sub] at hcz; linarith
        have hL := lip_add (c := 0) (g_lip (g t)) (dist_lip V) zero_le_one
        refine (sub_norm_le (y := y) (by positivity) hL ?_).trans ?_
        · intro w; have := hg' w; simpa [surrogate, hcz'] using this
        · simp; linarith
      · have hcz' : ¬ (g t) (x t) ≤ (g t) (z t) := by
          rw [map_sub] at hcz; intro h; exact hcz (by linarith)
        have hL := lip_add (c := c) (g_lip (g t)) (dist_lip V) zero_le_one
        refine (sub_norm_le (y := y) (by positivity) hL ?_).trans ?_
        · intro w; have := hg' w; simpa [surrogate, hcz', c] using this
        · linarith
    · by_cases hcz : g t (x t - z t) ≤ 0
      · have hcz' : (g t) (x t) ≤ (g t) (z t) := by rw [map_sub] at hcz; linarith
        have hL := lip_add (c := 0) (g_lip (g t)) (q_lip (q t) hq1) zero_le_one
        refine (sub_norm_le (y := y) (by positivity) hL ?_).trans ?_
        · intro w; have := hg' w; simpa [surrogate, hcz'] using this
        · simp; linarith
      · have hcz' : ¬ (g t) (x t) ≤ (g t) (z t) := by
          rw [map_sub] at hcz; intro h; exact hcz (by linarith)
        have hL := lip_add (c := c) (g_lip (g t)) (q_lip (q t) hq1) zero_le_one
        refine (sub_norm_le (y := y) (by positivity) hL ?_).trans ?_
        · intro w; have := hg' w; simpa [surrogate, hcz', c] using this
        · linarith
