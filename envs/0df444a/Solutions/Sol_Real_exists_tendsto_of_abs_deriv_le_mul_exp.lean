-- Prove2me | solution 1 for Real.exists_tendsto_of_abs_deriv_le_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T20:36:28.654936+00:00
-- url     : https://prove2.me/submissions/62893cad-2c65-49b3-992c-5b788f3c6311

import Mathlib

open scoped Topology
open Set Filter

namespace RH6

/-- a function whose derivative is bounded by `C e^{-δs}` converges -/
lemma exists_tendsto_of_abs_deriv_le {m m' : ℝ → ℝ} {s₀ C δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ s > s₀, HasDerivAt m (m' s) s)
    (hb : ∀ s > s₀, |m' s| ≤ C * Real.exp (-(δ * s))) :
    ∃ d : ℝ, Tendsto m atTop (𝓝 d) := by
  set K := C / δ with hK
  set e : ℝ → ℝ := fun s => K * Real.exp (-(δ * s)) with he
  have hde : ∀ s, HasDerivAt e (-(C * Real.exp (-(δ * s)))) s := by
    intro s
    have h1 : HasDerivAt (fun s => -(δ * s)) (-(δ * 1)) s :=
      ((hasDerivAt_id s).const_mul δ).neg
    have hδ' : δ ≠ 0 := hδ.ne'
    refine ((h1.exp).const_mul K).congr_deriv ?_
    simp only [hK]
    field_simp
  set D : Set ℝ := Ioi s₀ with hD
  have hDi : interior D = D := isOpen_Ioi.interior_eq
  -- `χ = m - e` is monotone, `ψ = m + e` is antitone
  have hχ : MonotoneOn (fun s => m s - e s) D := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi s₀)
      (fun s hs => ((hd s hs).sub (hde s)).continuousAt.continuousWithinAt) ?_ ?_
      (f' := fun s => m' s - -(C * Real.exp (-(δ * s))))
    · intro s hs; rw [hDi] at hs; exact ((hd s hs).sub (hde s)).hasDerivWithinAt
    · intro s hs; rw [hDi] at hs
      have := (abs_le.1 (hb s hs)).1; linarith
  have hψ : AntitoneOn (fun s => m s + e s) D := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi s₀)
      (fun s hs => ((hd s hs).add (hde s)).continuousAt.continuousWithinAt) ?_ ?_
      (f' := fun s => m' s + -(C * Real.exp (-(δ * s))))
    · intro s hs; rw [hDi] at hs; exact ((hd s hs).add (hde s)).hasDerivWithinAt
    · intro s hs; rw [hDi] at hs
      have := (abs_le.1 (hb s hs)).2; linarith
  set a := s₀ + 1 with ha
  have haD : a ∈ D := show s₀ < s₀ + 1 by linarith
  set χ' : ℝ → ℝ := fun s => m (max s a) - e (max s a) with hχ'
  have hmax : ∀ s, max s a ∈ D := fun s => show s₀ < max s a from
    lt_of_lt_of_le (show s₀ < a by linarith) (le_max_right _ _)
  have hmono : Monotone χ' := fun x y hxy =>
    hχ (hmax x) (hmax y) (max_le_max hxy le_rfl)
  have hbdd : BddAbove (range χ') := by
    refine ⟨m a + e a, ?_⟩
    rintro _ ⟨x, rfl⟩
    have h1 : e (max x a) ≥ 0 ∨ e (max x a) < 0 := le_or_gt 0 _
    have hψa := hψ haD (hmax x) (le_max_right x a)
    have hepos : 0 ≤ e (max x a) := by
      have hC : 0 ≤ C := by
        have := (abs_nonneg _).trans (hb a haD)
        exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
      exact mul_nonneg (div_nonneg hC hδ.le) (Real.exp_pos _).le
    simp only [hχ']
    linarith
  have hlim := tendsto_atTop_ciSup hmono hbdd
  have he0 : Tendsto e atTop (𝓝 0) := by
    have : Tendsto (fun s => -(δ * s)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hδ)
    simpa [he] using (Real.tendsto_exp_atBot.comp this).const_mul K
  refine ⟨⨆ i, χ' i, ?_⟩
  have hsum := hlim.add he0
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop a] with s hs
  simp only [hχ', max_eq_left hs]
  ring

end RH6

open Real

open Filter Topology

theorem solution {m m' : ℝ → ℝ} {s₀ C δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ s > s₀, HasDerivAt m (m' s) s)
    (hb : ∀ s > s₀, |m' s| ≤ C * Real.exp (-(δ * s))) :
    ∃ d : ℝ, Tendsto m atTop (𝓝 d) :=
  RH6.exists_tendsto_of_abs_deriv_le hδ hd hb
