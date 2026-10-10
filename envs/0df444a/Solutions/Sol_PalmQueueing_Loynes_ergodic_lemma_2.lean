-- Prove2me | solution 2 for PalmQueueing.Loynes.ergodic_lemma
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-10T05:00:20.579335+00:00
-- url     : https://prove2.me/submissions/4fdbb113-f320-4737-aa52-0ee8dee95b58

import Mathlib

/-!
# Lemma 2.2.1: the ergodic lemma behind Loynes' theorem (§2.2.3, p.87)
-/

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 2.2.1** (p.87). Let `Z` be non-negative, `P⁰`-a.s. finite, and such that
`Z − Z ∘ θ ∈ L¹(P⁰)`. Then `E⁰[Z − Z ∘ θ] = 0`.

The lemma is what makes the uniqueness half of Loynes' theorem work: applied to the difference of
two stationary solutions it forces that difference to be constant, and the flow's ergodicity then
forces it to be zero. The book's own proof is three lines — for any `C > 0`,
`|Z ∧ C − (Z ∧ C) ∘ θ| ≤ |Z − Z ∘ θ|`, and the conclusion follows from
`E⁰[Z ∧ C − (Z ∧ C) ∘ θ] = 0` and dominated convergence.

`Z` is `ℝ`-valued, so "`P⁰`-a.s. finite" is carried by the type. The hypothesis that matters and is
not automatic is the `θ`-invariance of `P⁰`, which Chapter 1's Eq. (1.2.16) supplies. -/
theorem solution (P0 : Measure Ω) [IsProbabilityMeasure P0]
    (shift : Ω → Ω) (hshift : Measurable shift) (hinv : Measure.map shift P0 = P0)
    (Z : Ω → ℝ) (hZmeas : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hint : Integrable (fun ω => Z ω - Z (shift ω)) P0) :
    ∫ ω, (Z ω - Z (shift ω)) ∂P0 = 0 := by
  have key : ∀ n : ℕ, ∫ ω, (min (Z ω) (n:ℝ) - min (Z (shift ω)) (n:ℝ)) ∂P0 = 0 := by
    intro n
    have hm : Measurable fun ω => min (Z ω) (n:ℝ) := hZmeas.min measurable_const
    have hb : Integrable (fun ω => min (Z ω) (n:ℝ)) P0 := by
      refine Integrable.of_bound hm.aestronglyMeasurable (n:ℝ)
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hZ0 ω) n.cast_nonneg)]
      exact min_le_right _ _
    have hb' : Integrable (fun ω => min (Z ω) (n:ℝ)) (Measure.map shift P0) := by
      rw [hinv]; exact hb
    have hcomp : ∫ ω, min (Z (shift ω)) (n:ℝ) ∂P0 = ∫ ω, min (Z ω) (n:ℝ) ∂P0 := by
      have := integral_map (μ := P0) hshift.aemeasurable
        (hm.aestronglyMeasurable (μ := Measure.map shift P0))
      rw [hinv] at this
      exact this.symm
    have hc : Integrable (fun ω => min (Z (shift ω)) (n:ℝ)) P0 := hb'.comp_measurable hshift
    rw [integral_sub hb hc, hcomp, sub_self]
  have hlim : Filter.Tendsto (fun n : ℕ => ∫ ω, (min (Z ω) (n:ℝ) - min (Z (shift ω)) (n:ℝ)) ∂P0)
      Filter.atTop (nhds (∫ ω, (Z ω - Z (shift ω)) ∂P0)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => |Z ω - Z (shift ω)|)
      (fun n => ?_) hint.abs (fun n => Filter.Eventually.of_forall fun ω => ?_)
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((hZmeas.min measurable_const).sub
        ((hZmeas.comp hshift).min measurable_const)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
      simp
    · obtain ⟨N, hN⟩ := exists_nat_ge (max (Z ω) (Z (shift ω)))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have h1 : Z ω ≤ n := (le_max_left _ _).trans (hN.trans (by exact_mod_cast hn))
      have h2 : Z (shift ω) ≤ n := (le_max_right _ _).trans (hN.trans (by exact_mod_cast hn))
      rw [min_eq_left h1, min_eq_left h2]
  simp only [key] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
