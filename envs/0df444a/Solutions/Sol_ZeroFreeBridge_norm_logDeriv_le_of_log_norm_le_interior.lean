-- Prove2me | solution 1 for ZeroFreeBridge.norm_logDeriv_le_of_log_norm_le_interior
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:59:58.554929+00:00
-- url     : https://prove2.me/submissions/978f2304-75bf-4911-95dc-519e94a5be91

import Mathlib
import Theorems.Thm_ZeroFreeBridge_log_branch_of_analytic_nonvanishing

/- PHASE 4 (dVP frontier, the CENTRE→EVALUATION-POINT transfer — item 3, the sole remaining hard core):
   bound the entire part `logDeriv g` at an INTERIOR point `z₀`, not just the centre.

   `DlvpBCDeriv.norm_deriv_le_of_re_le` bounds `‖logDeriv g c‖` at the disk CENTRE.  The dVP BC-SUM
   (`bc_sum_blaschke`) needs `‖logDeriv g z₀‖` at the EVALUATION point `z₀` (off-centre, `Re ≈ 1`).
   Borel–Carathéodory turns the one-sided oscillation bound `log‖g w‖ - log‖g c‖ ≤ M'` on `ball c R`
   into a TWO-sided value bound `‖h w - h c‖ ≤ 2M'‖w-c‖/(R-‖w-c‖)` (`h = log g`, `Re h = log‖g‖`), for
   EVERY interior `w` — not just on one sphere.  A Cauchy estimate on the sphere `‖w - z₀‖ = (R-ρ)/2`
   (`ρ = ‖z₀-c‖`), which lies inside `ball c R`, then bounds the derivative at `z₀`:

     `‖logDeriv g z₀‖ ≤ 4 M' (R + ρ) / (R - ρ)²`.

   The `2M'‖w‖/(R-‖w‖)` value bound is increasing in `‖w‖`, so on that sphere it is `≤ 2M'(R+ρ)/(R-ρ)`;
   dividing by the Cauchy radius `(R-ρ)/2` gives the stated constant.  With `M' = O(L)` and `ρ, R = O(1)`
   this is `O(L)` — exactly `bc_sum_blaschke`'s `Bg`.  conjecture1_proved = False (NOT a proof of RH).
-/


open Complex Metric

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge


theorem solution {g : ℂ → ℂ} {c z₀ : ℂ} {R M' : ℝ}
    (hM' : 0 < M') (hρ : ‖z₀ - c‖ < R)
    (hg : DifferentiableOn ℂ g (ball c R)) (hne : ∀ z ∈ ball c R, g z ≠ 0)
    (hbound : ∀ z ∈ ball c R, Real.log ‖g z‖ - Real.log ‖g c‖ ≤ M') :
    ‖logDeriv g z₀‖ ≤ 4 * M' * (R + ‖z₀ - c‖) / (R - ‖z₀ - c‖) ^ 2 := by
  set ρ := ‖z₀ - c‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hR : 0 < R := lt_of_le_of_lt hρ0 hρ
  have hRρ : 0 < R - ρ := by linarith
  set s := (R - ρ) / 2 with hsdef
  have hs : 0 < s := by rw [hsdef]; linarith
  have hsρR : s + ρ < R := by rw [hsdef]; linarith
  -- the analytic log branch h of g, with Re h = log‖g‖ and h' = logDeriv g
  obtain ⟨h, hderiv, _hhc, _hexp, hre⟩ := log_branch_of_analytic_nonvanishing hR hg hne
  have hmaps : ∀ w ∈ ball (0 : ℂ) R, c + w ∈ ball c R := by
    intro w hw; rw [mem_ball_zero_iff] at hw; rw [mem_ball_iff_norm]; simpa using hw
  -- centred, normalised f(w) = h(c+w) - h(c): f 0 = 0, Re f ≤ M', holomorphic on ball 0 R
  set f : ℂ → ℂ := fun w => h (c + w) - h c with hf_def
  have hf_diffR : DifferentiableOn ℂ f (ball 0 R) := by
    intro w hw
    have hcw : DifferentiableAt ℂ h (c + w) := (hderiv _ (hmaps w hw)).differentiableAt
    exact ((hcw.comp w (by fun_prop)).sub_const (h c)).differentiableWithinAt
  have hf0 : f 0 = 0 := by simp [hf_def]
  have hmaps_re : Set.MapsTo f (ball 0 R) {z | z.re ≤ M'} := by
    intro w hw
    simp only [Set.mem_setOf_eq, hf_def, Complex.sub_re]
    rw [hre (c + w) (hmaps w hw), hre c (mem_ball_self hR)]
    exact hbound _ (hmaps w hw)
  -- Borel–Carathéodory value bound on the whole disk
  have hBC : ∀ w ∈ ball (0 : ℂ) R, ‖f w‖ ≤ 2 * M' * ‖w‖ / (R - ‖w‖) := fun w hw =>
    Complex.borelCaratheodory_zero hM' hf_diffR hmaps_re hR hw hf0
  -- Cauchy sphere about ζ₀ = z₀ - c, radius s
  set ζ₀ := z₀ - c with hζ0def
  have hζ0norm : ‖ζ₀‖ = ρ := by rw [hζ0def]
  set C := 2 * M' * (R + ρ) / (R - ρ) with hCdef
  have hCsphere : ∀ w ∈ sphere ζ₀ s, ‖f w‖ ≤ C := by
    intro w hw
    rw [mem_sphere_iff_norm] at hw
    have hwnorm : ‖w‖ ≤ s + ρ := by
      calc ‖w‖ = ‖(w - ζ₀) + ζ₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
        _ = s + ρ := by rw [hw, hζ0norm]
    have hwlt : ‖w‖ < R := by linarith
    have hwball : w ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; exact hwlt
    have hbc := hBC w hwball
    have hRw : 0 < R - ‖w‖ := by linarith
    -- monotone: 2M'‖w‖/(R-‖w‖) ≤ 2M'(R+ρ)/(R-ρ) since ‖w‖ ≤ (R+ρ)/2
    have hmono : 2 * M' * ‖w‖ / (R - ‖w‖) ≤ C := by
      have hwle : 2 * ‖w‖ ≤ R + ρ := by rw [hsdef] at hwnorm; linarith
      have key : 0 ≤ 2 * M' * R * (R + ρ - 2 * ‖w‖) :=
        mul_nonneg (by positivity) (by linarith)
      rw [hCdef, div_le_div_iff₀ hRw hRρ]
      nlinarith [key]
    linarith
  -- assemble: f holomorphic up to the boundary of ball ζ₀ s ⊆ ball 0 R
  have hsub : closedBall ζ₀ s ⊆ ball (0 : ℂ) R := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw
    have : ‖w‖ ≤ s + ρ := by
      calc ‖w‖ = ‖(w - ζ₀) + ζ₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
        _ ≤ s + ρ := by rw [hζ0norm]; linarith
    rw [mem_ball_zero_iff]; linarith
  have hdcc : DiffContOnCl ℂ f (ball ζ₀ s) := by
    refine ⟨hf_diffR.mono ((ball_subset_closedBall).trans hsub), ?_⟩
    rw [closure_ball ζ₀ hs.ne']
    exact hf_diffR.continuousOn.mono hsub
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hs hdcc hCsphere
  -- deriv f ζ₀ = logDeriv g z₀
  have hz₀ball : z₀ ∈ ball c R := by rw [mem_ball_iff_norm]; exact hρ
  have hcζ : c + ζ₀ = z₀ := by rw [hζ0def]; ring
  have hbase : HasDerivAt h (logDeriv g z₀) (c + ζ₀) := hcζ ▸ hderiv z₀ hz₀ball
  have hf_deriv : HasDerivAt f (logDeriv g z₀) ζ₀ := (hbase.comp_const_add c ζ₀).sub_const (h c)
  rw [hf_deriv.deriv] at hcauchy
  -- C / s = 4 M' (R+ρ)/(R-ρ)²
  calc ‖logDeriv g z₀‖ ≤ C / s := hcauchy
    _ = 4 * M' * (R + ρ) / (R - ρ) ^ 2 := by rw [hCdef, hsdef]; field_simp; ring
