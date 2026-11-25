-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.end_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:15:22.302234+00:00
-- url     : https://prove2.me/submissions/0f45776f-0804-4c6d-a4dc-ed6ea9d206e6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_SetLIntegralBiUnionLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_pos_of_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_pos_of_notMem
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_mu_singleton
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (A : WeightedAtlas n Y ι La) (hn : 1 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {h : ι → Y → ℂ}
    (hint : ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-((n : ℝ) - 1 / 2)) *
      A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤) :
    ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ∂A.mu < ⊤ := by
  have : NullSingletonClass A.mu := ⟨fun x => A.mu_singleton hn x⟩
  have hS0 : A.mu (A.zeroSet s) = 0 := hD.finite_S.measure_zero A.mu
  obtain ⟨C, hC⟩ := hD.s_le_w
  set a : ℝ := (n : ℝ) - 1 / 2 with ha
  have hae : ∀ᵐ y ∂A.mu, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ≤
      ENNReal.ofReal (C ^ a) * ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-a) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS0] with y hyS
    have hs := A.sqn_pos_of_notMem (la := L) hyS
    have hw := A.sqn_pos_of_ne (la := L) (hD.no_common_zero y)
    have hCy := hC y
    have hCpos : 0 < C := by
      by_contra hc
      have hc' := not_lt.1 hc
      nlinarith
    have hna : 0 ≤ a := by
      have : (1:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have h1 : (C * A.sqn L w y) ^ (-a) ≤ A.sqn L s y ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hs hCy (by linarith)
    have h2 : A.sqn L w y ^ (-(n : ℝ)) =
        C ^ a * ((C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
      rw [Real.mul_rpow hCpos.le hw.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hCpos,
        mul_assoc, ← Real.rpow_add hw]
      have e1 : a + -a = 0 := by ring
      have e2 : -a + -(1 / 2 : ℝ) = -(n : ℝ) := by rw [ha]; ring
      rw [e1, e2, Real.rpow_zero, one_mul]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn0 := A.nsq_nonneg la h y
    have := Real.rpow_nonneg hw.le (-(1 / 2 : ℝ))
    have := Real.rpow_nonneg hCpos.le a
    rw [h2]
    calc A.nsq la h y * (C ^ a * ((C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))))
        = C ^ a * (A.nsq la h y * (C * A.sqn L w y) ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
          ring
      _ ≤ C ^ a * (A.nsq la h y * A.sqn L s y ^ (-a) * A.sqn L w y ^ (-(1 / 2 : ℝ))) := by
          gcongr
  calc ∫⁻ y, ENNReal.ofReal (A.nsq la h y * A.sqn L w y ^ (-(n : ℝ))) ∂A.mu
      ≤ ∫⁻ y, ENNReal.ofReal (C ^ a) * ENNReal.ofReal (A.nsq la h y * A.sqn L s y ^ (-a) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu := lintegral_mono_ae hae
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
