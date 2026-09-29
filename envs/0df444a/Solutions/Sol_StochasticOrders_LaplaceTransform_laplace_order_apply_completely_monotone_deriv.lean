-- Prove2me | solution 1 for StochasticOrders.LaplaceTransform.laplace_order_apply_completely_monotone_deriv
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T03:27:09.414711+00:00
-- url     : https://prove2.me/submissions/2e0fc3b4-eb45-4f75-93e2-ab638db11081

import Mathlib
import Definitions.Def_StochasticOrders_LaplaceTransform_LaplaceOrder
import Definitions.Def_StochasticOrders_LaplaceTransform_CompletelyMonotone

/-! Disproof of 8422d5bd
`StochasticOrders.LaplaceTransform.laplace_order_apply_completely_monotone_deriv`.

The hypothesis `CompletelyMonotone (deriv g)` constrains only `deriv g`, and `deriv` returns the
junk value `0` wherever `g` is not differentiable. The decreasing step
`g x = if x ≤ 1 then 2 else 1` is locally constant away from `1` and discontinuous at `1`, so
`deriv g = 0` everywhere, which is `C^∞` and completely monotone. With `X ≡ 0`, `Y ≡ 2` on the
one-point probability space, `X ≤Lt Y` holds, but `g ∘ X ≡ 2`, `g ∘ Y ≡ 1`, and at `s = 1`
the order would need `exp (-2) ≥ exp (-1)`, which is false. -/

set_option autoImplicit false

noncomputable def dp8422_g (x : ℝ) : ℝ := if x ≤ 1 then 2 else 1

theorem dp8422_not_contAt : ¬ ContinuousAt dp8422_g 1 := by
  intro hc
  have h1 : Filter.Tendsto dp8422_g (nhdsWithin 1 (Set.Ioi 1)) (nhds (dp8422_g 1)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto dp8422_g (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have : ¬ y ≤ 1 := not_le.mpr hy
    simp [dp8422_g, this]
  have h3 := tendsto_nhds_unique h1 h2
  simp [dp8422_g] at h3

theorem dp8422_deriv : deriv dp8422_g = fun _ => 0 := by
  funext x
  rcases lt_trichotomy x 1 with hx | hx | hx
  · have hev : dp8422_g =ᶠ[nhds x] fun _ => (2 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      have : y ≤ 1 := le_of_lt hy
      simp [dp8422_g, this]
    rw [hev.deriv_eq, deriv_const]
  · subst hx
    apply deriv_zero_of_not_differentiableAt
    intro hd
    exact dp8422_not_contAt hd.continuousAt
  · have hev : dp8422_g =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      have : ¬ y ≤ 1 := not_le.mpr hy
      simp [dp8422_g, this]
    rw [hev.deriv_eq, deriv_const]

open MeasureTheory StochasticOrders.LaplaceTransform in
theorem solution : ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXnn : ∀ ω, 0 ≤ X ω) (hYnn : ∀ ω, 0 ≤ Y ω) (g : ℝ → ℝ) (hgmeas : Measurable g)
    (hgpos : ∀ x, 0 ≤ x → 0 < g x) (hgderiv : CompletelyMonotone (deriv g))
    (h : LaplaceOrder μ ν X Y),
    LaplaceOrder μ ν (g ∘ X) (g ∘ Y)) := by
  intro H
  have hCM : CompletelyMonotone (deriv dp8422_g) := by
    rw [dp8422_deriv]
    refine ⟨contDiff_const, fun n x _ => ?_⟩
    simp
  have hmeas : Measurable dp8422_g :=
    Measurable.ite measurableSet_Iic measurable_const measurable_const
  have hpos : ∀ x, 0 ≤ x → 0 < dp8422_g x := by
    intro x _
    unfold dp8422_g
    split_ifs <;> norm_num
  have hLt : LaplaceOrder (Measure.dirac ()) (Measure.dirac ())
      (fun _ : Unit => (0 : ℝ)) (fun _ : Unit => (2 : ℝ)) := by
    intro s hs
    simp only [integral_dirac, mul_zero, neg_zero, Real.exp_zero]
    rw [ge_iff_le, Real.exp_le_one_iff]
    linarith
  have key := H (Measure.dirac ()) (Measure.dirac ()) (fun _ : Unit => (0 : ℝ))
    (fun _ : Unit => (2 : ℝ)) measurable_const measurable_const (fun _ => le_rfl)
    (fun _ => by norm_num) dp8422_g hmeas hpos hCM hLt 1 one_pos
  have hg0 : dp8422_g 0 = 2 := by simp [dp8422_g]
  have hg2 : dp8422_g 2 = 1 := by norm_num [dp8422_g]
  simp only [integral_dirac, Function.comp_apply, hg0, hg2, one_mul] at key
  rw [ge_iff_le, Real.exp_le_exp] at key
  linarith
