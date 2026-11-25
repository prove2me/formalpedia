-- Prove2me | solution 1 for PI.RhsWLim.W.PH.subst_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:47.915515+00:00
-- url     : https://prove2.me/submissions/f1bc284b-9cc8-42ec-97ad-2bb601a590a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.PH
namespace PI.RhsWLim.W.PH
theorem _root_.solution (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (X : ℝ → ℝ≥0∞)
    (hX : ∀ R ∈ Ioo 0 (Real.sqrt (T * T')), X R = 0) :
    ∫⁻ R in Ioi 0, X R = ∫⁻ ρ in Ioi 0,
      ENNReal.ofReal (|T * ρ / Real.sqrt (T * (ρ ^ 2 + T'))|) * X (Real.sqrt (T * (ρ ^ 2 + T'))) := by
  set q := Real.sqrt (T * T') with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hTT : 0 < T * T' := mul_pos hT hT'

  have e1 : ∫⁻ R in Ioi 0, X R = ∫⁻ R in Ioi q, X R := by
    rw [← Ioc_union_Ioi_eq_Ioi hq0, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl),
      ← setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := q)),
      setLIntegral_congr_fun measurableSet_Ioo (fun R hR => hX R hR), lintegral_zero, zero_add]
  rw [e1]
  set f : ℝ → ℝ := fun ρ => Real.sqrt (T * (ρ ^ 2 + T')) with hf
  have hpos : ∀ ρ : ℝ, 0 < T * (ρ ^ 2 + T') := fun ρ => by positivity
  have himage : f '' Ioi 0 = Ioi q := by
    ext R
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      simp only [mem_Ioi] at hρ ⊢
      apply Real.sqrt_lt_sqrt hTT.le
      have : 0 < T * ρ ^ 2 := by positivity
      nlinarith
    · intro hR
      simp only [mem_Ioi] at hR
      have hR0 : 0 < R := lt_of_le_of_lt hq0 hR
      have hR2 : T * T' < R ^ 2 := by
        have := (Real.sqrt_lt' hR0).1 hR
        linarith
      have hd : 0 < R ^ 2 / T - T' := by
        rw [sub_pos, lt_div_iff₀ hT]; linarith
      refine ⟨Real.sqrt (R ^ 2 / T - T'), Real.sqrt_pos.2 hd, ?_⟩
      simp only [hf]
      rw [Real.sq_sqrt hd.le, show T * (R ^ 2 / T - T' + T') = R ^ 2 by field_simp; ring,
        Real.sqrt_sq hR0.le]
  have hderiv : ∀ ρ ∈ Ioi (0 : ℝ), HasDerivWithinAt f (T * ρ / Real.sqrt (T * (ρ ^ 2 + T'))) (Ioi 0) ρ := by
    intro ρ hρ
    have h1 : HasDerivAt (fun x : ℝ => T * (x ^ 2 + T')) (T * (2 * ρ)) ρ := by
      have := ((hasDerivAt_pow 2 ρ).add_const T').const_mul T
      simpa using this
    have h2 := h1.sqrt (hpos ρ).ne'
    refine (h2.congr_deriv ?_).hasDerivWithinAt
    have : Real.sqrt (T * (ρ ^ 2 + T')) ≠ 0 := (Real.sqrt_pos.2 (hpos ρ)).ne'
    field_simp
  have hinj : InjOn f (Ioi 0) := by
    intro a ha b hb hab
    simp only [hf] at hab
    rw [Real.sqrt_inj (hpos a).le (hpos b).le] at hab
    have ha' : (0 : ℝ) < a := ha
    have hb' : (0 : ℝ) < b := hb
    have h2 : a ^ 2 = b ^ 2 := by
      have := mul_left_cancel₀ hT.ne' hab
      linarith
    exact le_antisymm (by nlinarith) (by nlinarith)
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj X]
end PI.RhsWLim.W.PH
