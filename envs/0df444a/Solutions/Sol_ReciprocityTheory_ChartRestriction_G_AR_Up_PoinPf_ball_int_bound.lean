-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.ball_int_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:42.573807+00:00
-- url     : https://prove2.me/submissions/850274f7-6d9a-4b96-ab05-5c9ad15c81d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_cpt_mem_dom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_exp_neg_phla
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_nfac_cpt_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
theorem _root_.solution (X : Data E r) (la : Wt X.Ψ r) {R0 ρ : ℝ}
    (hgood : ∀ w ∈ Metric.ball (0 : V (nd X)) R0, (∀ τ, (mat (nmat X w) τ).det ≠ 0) ∧
      (∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (lminor (Gw X w τ) i).re) ∧ 1 / 2 < nfw X la w)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hxo : IsOrth X x) (P : Frame X.Ψ r → ℂ) :
    Metric.ball (0 : V (nd X)) (min R0 ρ) ⊆ Bset X x ρ ∧
      ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x z)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
        ∫⁻ w in Bset X x ρ, ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
  have hgoodR := fun w (hw : w ∈ Metric.ball (0 : V (nd X)) (min R0 ρ)) =>
    hgood w (Metric.ball_subset_ball (min_le_left _ _) hw)
  have hmem : Metric.ball (0 : V (nd X)) (min R0 ρ) ⊆ Bset X x ρ := fun w hw => by
    obtain ⟨h1, h2, -⟩ := hgoodR w hw
    exact ⟨lt_of_lt_of_le (mem_ball_zero_iff.1 hw) (min_le_right _ _), cpt_mem_dom X hx hxo h1 h2⟩
  refine ⟨hmem, ?_⟩
  have hpt : ∀ w ∈ Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x w)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
      (‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by
    intro w hw
    obtain ⟨-, -, h3⟩ := hgoodR w hw
    have hn : X.nfac la (cpt X x w) = nfw X la w := nfac_cpt_orth X la hxo w
    have he : 1 ≤ ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
      rw [exp_neg_phla X la (by rw [hn]; linarith), hn, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    calc ‖P (cpt X x w)‖ₑ ^ 2 = ‖P (cpt X x w)‖ₑ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖P (cpt X x w)‖ₑ ^ 2 *
          (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by gcongr
      _ = _ := by ring
  calc ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ‖P (cpt X x z)‖ₑ ^ 2
      ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ), ENNReal.ofReal 4 *
          (‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z)))) :=
        setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
    _ = ENNReal.ofReal 4 * ∫⁻ z in Metric.ball (0 : V (nd X)) (min R0 ρ),
          ‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set hmem) zero_le
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
