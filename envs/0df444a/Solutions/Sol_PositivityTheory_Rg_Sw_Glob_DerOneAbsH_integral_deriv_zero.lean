-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.Glob.DerOneAbsH.integral_deriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:22:25.978245+00:00
-- url     : https://prove2.me/submissions/634142f9-0bcc-4ec5-a9ae-3ec84eb35456

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GlobalGaussLaws_DerOneAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory intervalIntegral
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.DerOneAbsH
namespace PositivityTheory.Rg.Sw.Glob.DerOneAbsH
theorem _root_.solution {X Ξ : Type*} [MeasurableSpace X] [Countable Ξ] [MeasurableSpace Ξ]
    [MeasurableSingletonClass Ξ] (m : Measure X) [SFinite m] (F F' : X → ℝ → Ξ → ℂ)
    (hd : ∀ x ξ, ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s => F x s ξ) (F' x t ξ) t)
    (hcont : ∀ x ξ, Continuous fun t => F' x t ξ)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod (volume.restrict (Set.Ioc 0 1))))
    (hfin : ∫⁻ p : X × ℝ, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod (volume.restrict (Set.Ioc 0 1))) ≠ ⊤)
    (hsum0 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 0 ξ‖) (hsum1 : ∀ᵐ x ∂m, Summable fun ξ => ‖F x 1 ξ‖)
    (hint0 : Integrable (fun x => ∑' ξ, F x 0 ξ) m) (hint1 : Integrable (fun x => ∑' ξ, F x 1 ξ) m)
    (hends : ∫ x, ∑' ξ, F x 1 ξ ∂m = ∫ x, ∑' ξ, F x 0 ξ ∂m)
    (hconst : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∫ x, ∑' ξ, F' x t ξ ∂m = ∫ x, ∑' ξ, F' x 0 ξ ∂m) :
    ∫ x, ∑' ξ, F' x 0 ξ ∂m = 0 := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  have hae : ∀ ξ, AEMeasurable (fun p : X × ℝ => ‖F' p.1 p.2 ξ‖ₑ) (m.prod μ) := fun ξ => (hmeas ξ).enorm
  have hle : ∀ ξ, ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) ≤ ∫⁻ p, ∑' ξ, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) :=
    fun ξ => lintegral_mono fun p => ENNReal.le_tsum ξ
  have hI : ∀ ξ, Integrable (fun p : X × ℝ => F' p.1 p.2 ξ) (m.prod μ) := fun ξ =>
    ⟨hmeas ξ, lt_of_le_of_lt (hle ξ) hfin.lt_top⟩
  have htsum : ∑' ξ, ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) ≠ ⊤ := by
    rw [← lintegral_tsum hae]; exact hfin

  have hftc : ∀ x ξ, ∫ t, F' x t ξ ∂μ = F x 1 ξ - F x 0 ξ := by
    intro x ξ
    rw [hμ, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (hd x ξ) ((hcont x ξ).intervalIntegrable 0 1)

  have hswap : ∀ ξ, ∫ x, (∫ t, F' x t ξ ∂μ) ∂m = ∫ t, (∫ x, F' x t ξ ∂m) ∂μ := fun ξ =>
    integral_integral_swap (f := fun x t => F' x t ξ) (hI ξ)

  have hbx : ∑' ξ, ∫⁻ x, ‖∫ t, F' x t ξ ∂μ‖ₑ ∂m ≠ ⊤ := by
    refine ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum fun ξ => ?_)
    calc ∫⁻ x, ‖∫ t, F' x t ξ ∂μ‖ₑ ∂m ≤ ∫⁻ x, ∫⁻ t, ‖F' x t ξ‖ₑ ∂μ ∂m :=
          lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) := (lintegral_prod _ (hae ξ)).symm
  have hbt : ∑' ξ, ∫⁻ t, ‖∫ x, F' x t ξ ∂m‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top htsum (ENNReal.tsum_le_tsum fun ξ => ?_)
    calc ∫⁻ t, ‖∫ x, F' x t ξ ∂m‖ₑ ∂μ ≤ ∫⁻ t, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ∂μ :=
          lintegral_mono fun t => enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ p, ‖F' p.1 p.2 ξ‖ₑ ∂(m.prod μ) := (lintegral_prod_symm _ (hae ξ)).symm
  have S1 : ∫ x, ∑' ξ, ∫ t, F' x t ξ ∂μ ∂m = ∑' ξ, ∫ x, ∫ t, F' x t ξ ∂μ ∂m :=
    integral_tsum (fun ξ => (hI ξ).integral_prod_left.aestronglyMeasurable) hbx
  have S2 : ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ = ∑' ξ, ∫ t, ∫ x, F' x t ξ ∂m ∂μ :=
    integral_tsum (fun ξ => (hI ξ).integral_prod_right.aestronglyMeasurable) hbt

  have hslice : ∀ᵐ t ∂μ, ∀ ξ, AEStronglyMeasurable (fun x => F' x t ξ) m := by
    rw [ae_all_iff]
    intro ξ
    exact ((hmeas ξ).prod_swap).prodMk_left
  have hfinT : ∀ᵐ t ∂μ, ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ≠ ⊤ := by
    have hmξ : ∀ ξ, AEMeasurable (fun t => ∫⁻ x, ‖F' x t ξ‖ₑ ∂m) μ := fun ξ => by
      simpa using ((hae ξ).prod_swap).lintegral_prod_right'
    have hm' : AEMeasurable (fun t => ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m) μ := AEMeasurable.tsum hmξ
    have : ∫⁻ t, ∑' ξ, ∫⁻ x, ‖F' x t ξ‖ₑ ∂m ∂μ ≠ ⊤ := by
      rw [lintegral_tsum hmξ]
      refine ne_top_of_le_ne_top htsum (le_of_eq (tsum_congr fun ξ => ?_))
      exact (lintegral_prod_symm _ (hae ξ)).symm
    filter_upwards [ae_lt_top' hm' this] with t ht using ht.ne
  have S3 : ∀ᵐ t ∂μ, ∫ x, ∑' ξ, F' x t ξ ∂m = ∑' ξ, ∫ x, F' x t ξ ∂m := by
    filter_upwards [hslice, hfinT] with t h1 h2 using integral_tsum h1 h2
  have hIoc : ∀ᵐ t ∂μ, t ∈ Set.Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc

  set c := ∫ x, ∑' ξ, F' x 0 ξ ∂m with hc
  have hμ1 : μ Set.univ = 1 := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Ioc]; simp
  have key : c = ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ := by
    have : ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ = ∫ _t, c ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [S3, hIoc] with t h1 h2
      rw [← h1, hconst t h2]
    rw [this, MeasureTheory.integral_const, Measure.real, hμ1, ENNReal.toReal_one, one_smul]
  have hsub : ∀ᵐ x ∂m, ∑' ξ, ∫ t, F' x t ξ ∂μ = ∑' ξ, F x 1 ξ - ∑' ξ, F x 0 ξ := by
    filter_upwards [hsum0, hsum1] with x h0 h1
    simp only [hftc]
    exact (h1.of_norm).tsum_sub h0.of_norm
  calc c = ∫ t, ∑' ξ, ∫ x, F' x t ξ ∂m ∂μ := key
    _ = ∑' ξ, ∫ t, ∫ x, F' x t ξ ∂m ∂μ := S2
    _ = ∑' ξ, ∫ x, ∫ t, F' x t ξ ∂μ ∂m := tsum_congr fun ξ => (hswap ξ).symm
    _ = ∫ x, ∑' ξ, ∫ t, F' x t ξ ∂μ ∂m := S1.symm
    _ = ∫ x, (∑' ξ, F x 1 ξ - ∑' ξ, F x 0 ξ) ∂m := integral_congr_ae hsub
    _ = ∫ x, ∑' ξ, F x 1 ξ ∂m - ∫ x, ∑' ξ, F x 0 ξ ∂m := integral_sub hint1 hint0
    _ = 0 := by rw [hends, sub_self]
end PositivityTheory.Rg.Sw.Glob.DerOneAbsH
