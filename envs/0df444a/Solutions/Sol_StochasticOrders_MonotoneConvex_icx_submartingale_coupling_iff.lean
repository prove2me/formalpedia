-- Prove2me | solution 1 for StochasticOrders.MonotoneConvex.icx_submartingale_coupling_iff
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:52:54.668254+00:00
-- url     : https://prove2.me/submissions/87352cac-a487-4294-923b-053b7f0a695e

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder

/-! Disproof of `StochasticOrders.MonotoneConvex.icx_submartingale_coupling_iff`.

Counterexample (forward direction fails): `X ≡ 1` on `(Unit, dirac ())` and `Y ω = ω⁻¹` on
`(ℝ, volume.restrict (Ioc 0 1))`. `Y ≥ 0` but `E Y = ∞`, so the only increasing convex `φ` with
`φ ∘ Y` integrable are constant on `[0, ∞)`, and `IcxOrder` holds with equality. Yet `Ŷ =st Y`
is not integrable, so `ρ[Ŷ | ·] = 0`, while `X̂ = 1` a.s.: the submartingale inequality fails. -/

namespace Cex76c76a50

open MeasureTheory ProbabilityTheory Set

/-- the probability measure for `Y`: Lebesgue measure on `(0, 1]` -/
noncomputable def νc : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

instance isProb_νc : IsProbabilityMeasure νc := ⟨by simp [νc]⟩

theorem not_integrable_inv : ¬ Integrable (fun ω : ℝ => ω⁻¹) νc := by
  intro h
  have h2 : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 h
  rw [intervalIntegrable_inv_iff] at h2
  rcases h2 with h2 | h2
  · norm_num at h2
  · exact h2 (by simp)

theorem inv_nonneg_ae : ∀ᵐ ω ∂νc, 0 ≤ ω⁻¹ := by
  unfold νc
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with ω hω
  exact inv_nonneg.2 hω.1.le

/-- A monotone convex `φ` whose composition with a nonnegative non-integrable variable is
integrable must be constant on `[0, ∞)`. -/
theorem const_of_integrable (φ : ℝ → ℝ) (hm : Monotone φ) (hc : ConvexOn ℝ univ φ)
    (hφ : Integrable (fun ω : ℝ => φ ω⁻¹) νc) (x : ℝ) (hx : 0 ≤ x) : φ x = φ 0 := by
  by_contra hne
  have hlt : φ 0 < φ x := lt_of_le_of_ne (hm hx) (Ne.symm hne)
  have hxpos : 0 < x := by
    rcases hx.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd rfl hne
  have hd : 0 < φ x - φ 0 := by linarith
  set c := x / (φ x - φ 0) with hcdef
  have hcpos : 0 < c := div_pos hxpos hd
  -- the key bound: `y ≤ x + (φ y - φ 0) * c` for every `y ≥ 0`
  have bound : ∀ y : ℝ, 0 ≤ y → y ≤ x + (φ y - φ 0) * c := by
    intro y hy
    rcases le_or_gt y x with hyx | hyx
    · have : 0 ≤ (φ y - φ 0) * c := mul_nonneg (by linarith [hm hy]) hcpos.le
      linarith
    · have hypos : 0 < y := lt_trans hxpos hyx
      have ha : 0 ≤ 1 - x / y := by
        rw [sub_nonneg, div_le_one hypos]; exact hyx.le
      have hb : 0 ≤ x / y := div_nonneg hx hypos.le
      have h := hc.2 (mem_univ 0) (mem_univ y) ha hb (by ring)
      have e1 : (1 - x / y) • (0 : ℝ) + (x / y) • y = x := by
        simp only [smul_eq_mul, mul_zero, zero_add]
        field_simp
      rw [e1] at h
      simp only [smul_eq_mul] at h
      have ht : y * (x / y) = x := by field_simp
      have key : y * (φ x - φ 0) ≤ x * (φ y - φ 0) := by
        have := mul_le_mul_of_nonneg_left h hypos.le
        have e2 : y * ((1 - x / y) * φ 0 + x / y * φ y) = y * φ 0 - x * φ 0 + x * φ y := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, mul_sub, mul_one, ht]; ring
        rw [e2] at this
        linarith
      have : y ≤ (φ y - φ 0) * c := by
        rw [hcdef, ← mul_div_assoc, le_div_iff₀ hd]; linarith
      linarith
  apply not_integrable_inv
  refine Integrable.mono' (g := fun ω : ℝ => x + (φ ω⁻¹ - φ 0) * c)
    ((integrable_const x).add ((hφ.sub (integrable_const _)).mul_const c))
    (measurable_inv.aestronglyMeasurable) ?_
  filter_upwards [inv_nonneg_ae] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω]
  exact bound _ hω

theorem icx : StochasticOrders.MonotoneConvex.IcxOrder (Measure.dirac ()) νc
    (fun _ : Unit => (1 : ℝ)) (fun ω : ℝ => ω⁻¹) := by
  intro φ hm hc _ hφ
  have hφ' : Integrable (fun ω : ℝ => φ ω⁻¹) νc := hφ
  have h1 : φ 1 = φ 0 := const_of_integrable φ hm hc hφ' 1 zero_le_one
  have hae : (fun ω : ℝ => φ ω⁻¹) =ᵐ[νc] fun _ => φ 0 := by
    filter_upwards [inv_nonneg_ae] with ω hω
    exact const_of_integrable φ hm hc hφ' _ hω
  rw [integral_congr_ae hae]
  simp [h1]

theorem no_coupling : ¬ ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'')
    (_ : IsProbabilityMeasure ρ) (Xhat Yhat : Ω'' → ℝ),
    IdentDistrib Xhat (fun _ : Unit => (1 : ℝ)) ρ (Measure.dirac ()) ∧
    IdentDistrib Yhat (fun ω : ℝ => ω⁻¹) ρ νc ∧
    Xhat ≤ᵐ[ρ] ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] := by
  rintro ⟨Ω'', _, ρ, _, Xhat, Yhat, h1, h2, h3⟩
  have hYn : ¬ Integrable Yhat ρ := fun h => not_integrable_inv (h2.integrable_iff.1 h)
  rw [condExp_of_not_integrable hYn] at h3
  have hX1 : ∀ᵐ ω ∂ρ, Xhat ω ∈ ({1} : Set ℝ) :=
    h1.symm.ae_mem_snd (measurableSet_singleton 1) (Filter.Eventually.of_forall fun _ => rfl)
  have hF : ∀ᵐ _ω ∂ρ, False := by
    filter_upwards [h3, hX1] with ω h h'
    rw [Set.mem_singleton_iff] at h'
    simp only [Pi.zero_apply] at h
    linarith
  obtain ⟨_, h⟩ := hF.exists
  exact h

end Cex76c76a50

open MeasureTheory ProbabilityTheory StochasticOrders.MonotoneConvex in
theorem solution : ¬ (∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ),
    IcxOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧
        Xhat ≤ᵐ[ρ] ρ[Yhat | MeasurableSpace.comap Xhat inferInstance] ∧
        (∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ t : ℝ,
          (condDistrib Yhat Xhat ρ x₁) {y : ℝ | t < y} ≤
            (condDistrib Yhat Xhat ρ x₂) {y : ℝ | t < y})) := by
  intro h
  obtain ⟨Ω'', m, ρ, hρ, Xhat, Yhat, h1, h2, h3, -⟩ :=
    (h (Measure.dirac ()) Cex76c76a50.νc (fun _ : Unit => (1 : ℝ)) (fun ω : ℝ => ω⁻¹)).1
      Cex76c76a50.icx
  exact Cex76c76a50.no_coupling ⟨Ω'', m, ρ, hρ, Xhat, Yhat, h1, h2, h3⟩
