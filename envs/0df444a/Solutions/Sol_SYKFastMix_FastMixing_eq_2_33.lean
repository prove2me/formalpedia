-- Prove2me | solution 1 for SYKFastMix.FastMixing.eq_2_33
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:07:39.327199+00:00
-- url     : https://prove2.me/submissions/f71944d9-3094-4d30-a718-a98de8d70f8a

import Mathlib
import Theorems.Thm_SYKFastMix_FastMixing_eq_2_32

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder
open SYKFastMix.FastMixing

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {N : ℕ} (H : Mat ι) (γ : Fin N → Mat ι) (hH : H.IsHermitian)
    (hγ : ∀ i, (γ i).IsHermitian) (β rate : ℝ) (hβ : 0 ≤ β) (hrate : 0 < rate)
    (hgap : HasGap (discriminant H γ β) (gibbsRoot H β) rate) :
  (∀ τ : ℝ, 0 ≤ τ → ∀ X, IsDensity X →
    traceNorm (evolve (lindblad H γ β) τ X - gibbs H β) ≤
      Real.exp (-rate * τ) * Real.sqrt (Fintype.card ι : ℝ) * Real.exp (β * SYKEdge.opNorm H)) ∧
  (∀ ε : ℝ, 0 < ε → ε < 1 →
    mixingTime (lindblad H γ β) (gibbs H β) ε ≤
      ENNReal.ofReal ((1 / rate) * ((1/2 : ℝ) * Real.log (Fintype.card ι : ℝ) +
        β * SYKEdge.opNorm H + Real.log (1/ε)))) := by
  have hc := eq_2_32 H γ hH hγ β rate hβ hrate hgap
  refine ⟨hc, ?_⟩
  intro ε hε hε1
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos (α := ι))
  have hd1 : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos (α := ι))
  let τ : ℝ := (1 / rate) * ((1/2 : ℝ) * Real.log d +
    β * SYKEdge.opNorm H + Real.log (1/ε))
  have hτ : 0 ≤ τ := by
    have hn : 0 ≤ SYKEdge.opNorm H := norm_nonneg _
    have hlog : 0 ≤ Real.log (1/ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    exact mul_nonneg (one_div_nonneg.mpr hrate.le)
      (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hd1))
        (mul_nonneg hβ hn)) hlog)
  apply sInf_le
  refine ⟨τ, hτ, rfl, ?_⟩
  intro X hX
  refine (hc τ hτ X hX).trans ?_
  have hsqrt : Real.sqrt d = Real.exp ((1/2 : ℝ) * Real.log d) := by
    calc
      Real.sqrt d = Real.exp (Real.log (Real.sqrt d)) :=
        (Real.exp_log (Real.sqrt_pos.mpr hd)).symm
      _ = Real.exp ((1/2 : ℝ) * Real.log d) := by rw [Real.log_sqrt hd.le]; congr 1; ring
  change Real.exp (-rate * τ) * Real.sqrt d * Real.exp (β * SYKEdge.opNorm H) ≤ ε
  rw [hsqrt, ← Real.exp_add, ← Real.exp_add]
  have he : -rate * τ + (1/2 : ℝ) * Real.log d + β * SYKEdge.opNorm H = Real.log ε := by
    dsimp [τ]
    simp only [one_div, Real.log_inv]
    field_simp [hrate.ne']
    ring
  rw [he, Real.exp_log hε]
