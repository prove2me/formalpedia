-- Prove2me | solution 2 for ZipkinLostSales.LNatural.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:24.579863+00:00
-- url     : https://prove2.me/submissions/207b13a2-1d98-42e8-b3ad-42be2110027e

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
import Theorems.Thm_ZipkinLostSales_LNatural_gbar_lnatconvex
import Theorems.Thm_ZipkinLostSales_LNatural_lemma_2

-- carved verbatim out of submission 0c9de1ae-77d3-4255-b80f-cb877dda882d, lines 890-896

section
open MeasureTheory
open ZipkinLostSales
open ZipkinLostSales.LNatural

theorem qhat_nonneg (hh p u : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p) : 0 ≤ qhat hh p u := by
  unfold qhat
  exact add_nonneg (mul_nonneg hhh (le_max_right _ _)) (mul_nonneg hp (le_max_right _ _))

theorem gstep_nonneg {L : ℕ} (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ : 0 ≤ γ)
    (μ : Measure ℝ) (F : (Fin L → ℝ) → ℝ) (hF : ∀ v, 0 ≤ F v) (v : Fin L → ℝ) {ζ : ℝ}
    (hζ : ζ ≤ 0) : 0 ≤ gstep c hh p γ μ F v ζ := by
  unfold gstep qhat0
  have h1 : γ ^ L * c * ζ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hζ
  have h2 : 0 ≤ ∫ d, qhat hh p (vext v 0 - vext v 1 - d) ∂μ :=
    integral_nonneg fun d => qhat_nonneg hh p _ hhh hp
  have h3 : 0 ≤ ∫ d, F (next v d ζ) ∂μ := integral_nonneg fun d => hF _
  have := mul_nonneg hγ h3
  linarith

theorem nonempty_Iic0 : Nonempty (Set.Iic (0:ℝ)) := ⟨⟨0, Set.mem_Iic.2 le_rfl⟩⟩

theorem fbar_nonneg {L : ℕ} (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ : 0 ≤ γ)
    (μ : Measure ℝ) : ∀ k (v : Fin L → ℝ), 0 ≤ fbar c hh p γ μ k v := by
  intro k
  induction k with
  | zero => intro v; simp [fbar_zero]
  | succ k ih =>
    intro v
    rw [fbar_succ]
    have := nonempty_Iic0
    exact le_ciInf fun ζ => gstep_nonneg c hh p γ hc hhh hp hγ μ _ ih v ζ.2

theorem theorem_4_core (L : ℕ) (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ)
    (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (k : ℕ) :
    LNatConvexOn (V L) (fbar c hh p γ μ k) ∧
      LNatConvexOn (VxNeg L) (liftG (gbar c hh p γ μ k)) := by
  have hf : ∀ k, LNatConvexOn (V L) (fbar c hh p γ μ k) := by
    intro k
    induction k with
    | zero =>
      intro w _ w' _
      simp only [fbar_zero]
      norm_num
    | succ k ih =>
      have hg := ZipkinLostSales.LNatural.gbar_lnatconvex L hL μ hμ hμint c hh p γ hc hhh hp hγ0 hγ1 k ih
      have := ZipkinLostSales.LNatural.lemma_2 L hL (gbar c hh p γ μ k) hg (fun v _ => ⟨0, by
        rintro _ ⟨ζ, hζ, rfl⟩
        exact gstep_nonneg c hh p γ hc hhh hp hγ0.le μ _
          (fbar_nonneg c hh p γ hc hhh hp hγ0.le μ k) v hζ⟩)
      have e : fbar (L := L) c hh p γ μ (k + 1) = fun v => ⨅ ζ : Set.Iic (0:ℝ), gbar c hh p γ μ k v ζ := by
        funext v; rfl
      rw [e]; exact this
  exact ⟨hf k, ZipkinLostSales.LNatural.gbar_lnatconvex L hL μ hμ hμint c hh p γ hc hhh hp hγ0 hγ1 k (hf k)⟩

end

section
open MeasureTheory
open ZipkinLostSales.LNatural

theorem solution (L : ℕ) (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ)
    (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (k : ℕ) :
    LNatConvexOn (V L) (fbar c hh p γ μ k) ∧
      LNatConvexOn (VxNeg L) (liftG (gbar c hh p γ μ k)) := by
  exact theorem_4_core L hL μ hμ hμint c hh p γ hc hhh hp hγ0 hγ1 k

end
