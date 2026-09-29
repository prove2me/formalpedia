-- Prove2me | solution 1 for PerronKernels.integrable_inv_denom
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:03:02.46376+00:00
-- url     : https://prove2.me/submissions/24c43209-0eac-46f4-ba20-fdfe001e7b26

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.SW.Kernel =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The SW rung, wave S1 — the smoothed Mellin/Perron kernel identity

The reusable analytic core of the `sw` rung's smoothed Perron machinery
(`docs/blueprints/sw.md`, Riesz amendment).  The Riesz mean `ψ₁(x,χ)` has
Mellin kernel `x^{s+1}/(s(s+1))` with `1/|s|²` decay, so its vertical integral
converges *absolutely* and its target profile `y ↦ (1-1/y)₊` is *continuous* —
exactly what mathlib's `MellinInversion` machinery serves (the discontinuous
sharp-cutoff Perron step is what it cannot do).

## Route (assessed: MellinInversion, option (a) of the blueprint — chosen)

We take `f := (1 - ·)₊` (`kern`), compute `mellin f s = 1/(s(s+1))` for
`Re s > 0` (the Beta-type integral `∫₀¹ t^{s-1}(1-t) dt = 1/s - 1/(s+1)`,
`hasMellin_kern`), verify the three hypotheses of `mellinInv_mellin_eq`
(`MellinConvergent`, `VerticalIntegrable`, `ContinuousAt` — the latter free,
`kern` is continuous), and instantiate the inversion **at `x = 1/y`**: mathlib's
`mellinInv` carries a *negative* exponent `x^{-s}`, and `reflect` turns
`(1/y)^{-s}` into the `y^{+s}` we want.  The direct two-pole contour (option
(b)) was not needed — the convention match with `MellinInversion` is clean.

## Main results

* `kernel_identity` — `(1/2π) ∫_ℝ y^{c+ti}/((c+ti)(c+ti+1)) dt = (1-1/y)₊`,
  for `y > 0`, `c > 0`.  (`•` is the real scalar action on `ℂ`; exponents are
  `Complex.cpow`; the `1/(2πi)∫ds` becomes `1/(2π)∫dt` after `ds = i·dt`.)
* `hasMellin_kern` — the companion `mellin (1-·)₊ s = 1/(s(s+1))` (+ convergence).
* `verticalIntegrable_mellin_kern` — the vertical absolute-convergence lemma
  (integrand dominated by `(c²+t²)⁻¹`, itself scaled `integrable_inv_one_add_sq`).
* `kernel_sum_swap` — the S1b interface: the dominated sum↔integral swap
  `∑ₙ ∫ aₙ(x/n)^{s}/(...) = ∫ (∑ₙ aₙ(x/n)^{s})/(...)`, under the domination
  hypothesis `Summable (fun n => ‖a n‖·(x/n)^c)` (holds in the `c > 1`,
  `‖a n‖ ≲ log n` regime; the `L'/L` connection is deferred to S1b).

All four are axiom-clean (`propext, Classical.choice, Quot.sound`); no
`native_decide`, no new axioms, no `sorry`.  Imports Mathlib only —
independent of `Salt/SW/Defs.lean`.
-/


open MeasureTheory Complex Set

noncomputable section
namespace Salt.SW

/-- The smoothing profile `t ↦ (1 - t)₊`, ℂ-valued. Continuous everywhere;
supported on `(-∞, 1]`; on `Ioi 0` it agrees with `1[Ioc 0 1]·(1 - t)`. -/
def kern : ℝ → ℂ := fun t => ((max 0 (1 - t) : ℝ) : ℂ)

lemma continuous_kern : Continuous kern :=
  Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.sub continuous_id))

lemma kern_eq_indicator_diff {t : ℝ} (ht : 0 < t) :
    kern t = Set.indicator (Ioc 0 1) (fun _ => (1 : ℂ)) t
           - Set.indicator (Ioc 0 1) (fun u : ℝ => (u : ℂ)) t := by
  simp only [kern]
  by_cases h : t ≤ 1
  · have hmem : t ∈ Ioc (0:ℝ) 1 := ⟨ht, h⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
      max_eq_right (by linarith : (0:ℝ) ≤ 1 - t)]
    push_cast; ring
  · rw [not_le] at h
    have hnot : t ∉ Ioc (0:ℝ) 1 := by
      simp only [Set.mem_Ioc, not_and, not_le]; intro _; exact h
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot,
      max_eq_left (by linarith : (1:ℝ) - t ≤ 0)]
    push_cast; ring

/-- Companion identity: `mellin (1-·)₊ s = 1/(s(s+1))` for `Re s > 0`, together
with Mellin-convergence.  Beta-type integral `∫₀¹ t^{s-1}(1-t) = 1/s - 1/(s+1)`. -/
lemma hasMellin_kern {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent kern s ∧ mellin kern s = 1 / (s * (s + 1)) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre : (s + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re] at hre
    linarith
  have h1 := hasMellin_one_Ioc hs
  have h2 := hasMellin_cpow_Ioc (s := s) (1 : ℂ) (by rw [Complex.one_re]; linarith)
  simp only [Complex.cpow_one] at h2
  have hsub := hasMellin_sub h1.1 h2.1
  rw [h1.2, h2.2] at hsub
  refine ⟨?_, ?_⟩
  · rw [MellinConvergent]
    refine hsub.1.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [kern_eq_indicator_diff ht]
  · have hmel : mellin kern s = mellin (fun t => Set.indicator (Ioc 0 1) (fun _ => (1:ℂ)) t
        - Set.indicator (Ioc 0 1) (fun u : ℝ => (u:ℂ)) t) s := by
      simp only [mellin]
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      simp only [kern_eq_indicator_diff ht]
    rw [hmel, hsub.2]
    field_simp
    ring

/-! ## Deliverable 2 — vertical absolute convergence -/

lemma s_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : ((c:ℂ) + (t:ℂ) * I) ≠ 0 := by
  have hre : ((c:ℂ) + (t:ℂ) * I).re = c := by simp
  intro h; rw [h] at hre; simp at hre; linarith

lemma s1_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) : ((c:ℂ) + (t:ℂ) * I + 1) ≠ 0 := by
  have hre : ((c:ℂ) + (t:ℂ) * I + 1).re = c + 1 := by simp
  intro h; rw [h] at hre; simp at hre; linarith

lemma integrable_inv_c_sq_add_sq {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) := by
  have hg : Integrable (fun u : ℝ => (c ^ 2)⁻¹ * (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul ((c ^ 2)⁻¹)
  have hcomp : Integrable (fun t : ℝ => (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹) :=
    (integrable_comp_mul_left_iff (fun u => (c ^ 2)⁻¹ * (1 + u ^ 2)⁻¹)
      (inv_ne_zero hc.ne')).2 hg
  refine hcomp.congr ?_
  filter_upwards with t
  have hcne : c ≠ 0 := hc.ne'
  have hne : c ^ 2 + t ^ 2 ≠ 0 := by positivity
  field_simp

lemma norm_inv_denom_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(((c:ℂ) + (t:ℂ) * I) * ((c:ℂ) + (t:ℂ) * I + 1))⁻¹‖ ≤ (c ^ 2 + t ^ 2)⁻¹ := by
  have hns : ‖(c:ℂ) + (t:ℂ) * I‖ = Real.sqrt (c ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hns1 : ‖(c:ℂ) + (t:ℂ) * I + 1‖ = Real.sqrt ((c + 1) ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp
  have hle : c ^ 2 + t ^ 2 ≤ ‖(c:ℂ) + (t:ℂ) * I‖ * ‖(c:ℂ) + (t:ℂ) * I + 1‖ := by
    rw [hns, hns1]
    calc c ^ 2 + t ^ 2
        = Real.sqrt ((c ^ 2 + t ^ 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((c ^ 2 + t ^ 2) * ((c + 1) ^ 2 + t ^ 2)) := by
            apply Real.sqrt_le_sqrt; nlinarith [sq_nonneg t, hc.le, sq_nonneg c]
      _ = Real.sqrt (c ^ 2 + t ^ 2) * Real.sqrt ((c + 1) ^ 2 + t ^ 2) :=
            Real.sqrt_mul (by positivity) _
  rw [norm_inv, norm_mul]
  gcongr

lemma integrable_inv_denom {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (((c:ℂ) + (t:ℂ) * I) * ((c:ℂ) + (t:ℂ) * I + 1))⁻¹) := by
  refine (integrable_inv_c_sq_add_sq hc).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply Continuous.inv₀
    · fun_prop
    · intro t; exact mul_ne_zero (s_ne_zero hc t) (s1_ne_zero hc t)
  · filter_upwards with t; exact norm_inv_denom_le hc t

lemma verticalIntegrable_mellin_kern {c : ℝ} (hc : 0 < c) :
    Complex.VerticalIntegrable (mellin kern) c := by
  rw [Complex.VerticalIntegrable]
  refine (integrable_inv_denom hc).congr ?_
  filter_upwards with t
  have hsre : 0 < ((c:ℂ) + (t:ℂ) * I).re := by simp; linarith
  rw [(hasMellin_kern hsre).2, one_div]

/-! ## Deliverable 1 — the kernel identity -/

/-- Reflection across the imaginary axis: `(1/y)^{-s} = y^{s}` for `y > 0`.
This is what lets us instantiate mathlib's `mellinInv` (negative exponent) at
`x = 1/y` to recover the positive-exponent `y^{s}` we want. -/
lemma reflect {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ((1 / y : ℝ) : ℂ) ^ (-s) = (y : ℂ) ^ s := by
  have h1 : ((1 / y : ℝ) : ℂ) = ((y : ℂ))⁻¹ := by push_cast; ring
  have harg : ((y : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne
  rw [h1, Complex.cpow_neg, Complex.inv_cpow (y : ℂ) s harg, inv_inv]

/-- The truncated Perron value: `kern (1/y) = (1 - 1/y)₊`. -/
lemma kern_value {y : ℝ} (hy : 0 < y) :
    kern (1 / y) = if 1 ≤ y then (1 - 1 / (y : ℂ)) else 0 := by
  simp only [kern]
  by_cases h : 1 ≤ y
  · rw [if_pos h]
    have hle : (1 : ℝ) / y ≤ 1 := by rw [div_le_one hy]; exact h
    rw [max_eq_right (by linarith : (0:ℝ) ≤ 1 - 1 / y)]
    push_cast; ring
  · rw [if_neg h]
    rw [not_le] at h
    have hge : (1 : ℝ) ≤ 1 / y := by rw [le_div_iff₀ hy]; linarith
    rw [max_eq_left (by linarith : (1:ℝ) - 1 / y ≤ 0)]
    simp

/-- **The smoothed Mellin/Perron kernel identity.**  For `y > 0` and any vertical
line `Re s = c > 0`,
`(1/2π) ∫_ℝ y^{c+ti} / ((c+ti)(c+ti+1)) dt = (1 - 1/y)₊`.
(The `1/(2πi) ∫ ds` of the blueprint becomes `1/(2π) ∫ dt` after `ds = i dt`;
`•` is the real scalar action on `ℂ`.  Exponents are `Complex.cpow`.) -/
theorem kernel_identity {y : ℝ} (hy : 0 < y) {c : ℝ} (hc : 0 < c) :
    (1 / (2 * Real.pi)) • ∫ t : ℝ,
        (y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I) /
          (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))
      = if 1 ≤ y then (1 - 1 / (y : ℂ)) else 0 := by
  have hx : (0 : ℝ) < 1 / y := by positivity
  have hcre : 0 < ((c : ℂ)).re := by simpa using hc
  have hMC : MellinConvergent kern (↑c) := (hasMellin_kern hcre).1
  have hVI : Complex.VerticalIntegrable (mellin kern) c := verticalIntegrable_mellin_kern hc
  have hCont : ContinuousAt kern (1 / y) := continuous_kern.continuousAt
  have key := mellinInv_mellin_eq c kern hx hMC hVI hCont
  rw [kern_value hy] at key
  rw [← key, mellinInv]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs_def
  have hsre : 0 < s.re := by rw [hs_def]; simpa using hc
  rw [(hasMellin_kern hsre).2, reflect hy s, smul_eq_mul, mul_one_div]

/-! ## Deliverable 3 — the sum ↔ integral swap (S1b interface) -/

/-- `‖(b)^{c+ti}‖ = b^c` for `b ≥ 0`, `c > 0` (constant along the vertical line). -/
lemma norm_ofReal_cpow_vert {b : ℝ} (hb : 0 ≤ b) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖(b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)‖ = b ^ c := by
  rcases eq_or_lt_of_le hb with h | h
  · rw [← h, Complex.ofReal_zero, Complex.zero_cpow (s_ne_zero hc t), norm_zero,
      Real.zero_rpow hc.ne']
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos h]; simp

/-- Each summand `t ↦ w · b^{c+ti}/((c+ti)(c+ti+1))` is integrable on the line. -/
lemma integrable_Fterm (w : ℂ) {b : ℝ} (hb : 0 ≤ b) {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · have : (fun t : ℝ => w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) = fun _ => 0 := by
      funext t
      rw [← hb0, Complex.ofReal_zero, Complex.zero_cpow (s_ne_zero hc t)]; ring
    rw [this]; exact integrable_zero _ _ _
  · refine ((integrable_inv_c_sq_add_sq hc).const_mul (‖w‖ * b ^ c)).mono' ?_ ?_
    · apply Continuous.aestronglyMeasurable
      refine Continuous.div (continuous_const.mul (Continuous.const_cpow (by fun_prop)
        (Or.inl (Complex.ofReal_ne_zero.mpr hbpos.ne')))) (by fun_prop) ?_
      intro t; exact mul_ne_zero (s_ne_zero hc t) (s1_ne_zero hc t)
    · filter_upwards with t
      calc ‖w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
              / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))‖
          = (‖w‖ * b ^ c) * ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))⁻¹‖ := by
            rw [norm_div, norm_mul, norm_ofReal_cpow_vert hbpos.le hc, norm_inv]; ring
        _ ≤ (‖w‖ * b ^ c) * (c ^ 2 + t ^ 2)⁻¹ := by
            gcongr; exact norm_inv_denom_le hc t

/-- **The summed form (S1b interface).**  For `c > 0`, `x > 0`, and a coefficient
sequence `a` whose Dirichlet-weighted tail `∑ ‖a n‖·(x/n)^c` converges (the `c > 1`,
`‖a n‖ ≲ log n` regime — deferred to S1b), the per-term kernel integrals sum to the
single vertical integral of the Dirichlet series against the kernel:
`∑ₙ ∫ aₙ (x/n)^{c+ti}/(...) = ∫ (∑ₙ aₙ (x/n)^{c+ti})/(...)`.
This is the dominated sum↔integral swap; the `L'/L` connection is S1b's job. -/
theorem kernel_sum_swap (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c)
    (hsum : Summable (fun n : ℕ => ‖a n‖ * (x / n) ^ c)) :
    ∑' n : ℕ, (∫ t : ℝ, a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
      = ∫ t : ℝ, (∑' n : ℕ, a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
  have hb : ∀ n : ℕ, (0 : ℝ) ≤ x / n := fun n => by positivity
  have hInt : ∀ n : ℕ, Integrable (fun t : ℝ => a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) :=
    fun n => integrable_Fterm (a n) (hb n) hc
  have hSum : Summable (fun n : ℕ => ∫ t : ℝ, ‖a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))‖) := by
    have heq : (fun n : ℕ => ∫ t : ℝ, ‖a n * ((x / n : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))‖)
        = fun n : ℕ => (‖a n‖ * (x / n) ^ c)
            * ∫ t : ℝ, ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))⁻¹‖ := by
      funext n
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      dsimp only
      rw [norm_div, norm_mul, norm_ofReal_cpow_vert (hb n) hc, norm_inv]; ring
    rw [heq]; exact hsum.mul_right _
  rw [integral_tsum_of_summable_integral_norm hInt hSum]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [tsum_div_const]

end Salt.SW

end

end




section
open MeasureTheory Complex Set

theorem solution {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (((c:ℂ) + (t:ℂ) * I) * ((c:ℂ) + (t:ℂ) * I + 1))⁻¹) := by
  apply Salt.SW.integrable_inv_denom <;> assumption

end

