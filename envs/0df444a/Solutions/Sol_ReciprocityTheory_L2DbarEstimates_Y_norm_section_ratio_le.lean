-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.norm_section_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:32:04.230548+00:00
-- url     : https://prove2.me/submissions/4defb833-795a-4591-8d58-a7922e9d75da

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IteratedFDerivEqZeroOfIsBigO
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_VanishingOrderTransfer
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_weight_nsmul_eq_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {N' : ℕ} (A : WeightedAtlas n Y ι La) (L : La) (m : ℕ)
    (w : Fin N' → ι → Y → ℂ) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (Nsec : ι → Y → ℂ)
    (C1 C2 : ℝ) (h1 : ∀ y, A.nsq (m • L) Nsec y ≤ C1 * A.sqn L w y ^ m)
    (h2 : ∀ y, A.sqn L w y ≤ C2 * (A.nsq L w0 y + A.sqn L s y)) (y : Y)
    (hy0 : w0 (A.pick y) y ≠ 0) :
    ‖Nsec (A.pick y) y / w0 (A.pick y) y ^ m‖ ≤
      Real.sqrt (max C1 0 * |C2| ^ m) * (1 + ‖A.zmap w0 s y‖ ^ 2) ^ ((m : ℝ) / 2) := by
  set p := A.pick y with hp
  set E := Real.exp (-A.ph L p y) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hw0n : 0 < ‖w0 p y‖ := norm_pos_iff.2 hy0
  set a := ‖w0 p y‖ ^ 2 * E with ha
  have ha0 : 0 < a := by positivity
  set t := 1 + ‖A.zmap w0 s y‖ ^ 2 with ht
  have ht0 : 0 < t := by positivity
  set U := Nsec p y / w0 p y ^ m with hU
  have hsq : A.sqn L s y = a * ‖A.zmap w0 s y‖ ^ 2 := by
    simp only [sqn, nsq, zmap, EuclideanSpace.norm_sq_eq, ← hp, ← hE, ha,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [norm_div]
    field_simp
  have hw0sq : A.nsq L w0 y = a := rfl
  have hNsq : A.nsq (m • L) Nsec y = ‖U‖ ^ 2 * a ^ m := by
    simp only [nsq, ← hp]
    rw [weight_nsmul_eq_mul A L m p y (A.mem_pick y), show -(↑m * A.ph L p y) = ↑m * (-A.ph L p y)
      by ring, Real.exp_nat_mul, ← hE, hU, ha, norm_div, norm_pow]
    field_simp
    ring_nf
  have hsqw : 0 ≤ A.sqn L w y :=
    Finset.sum_nonneg (fun k _ => by unfold nsq; positivity)
  have hle : ‖U‖ ^ 2 * a ^ m ≤ (max C1 0 * |C2| ^ m * t ^ m) * a ^ m := by
    rw [← hNsq]
    have hb : A.sqn L w y ≤ |C2| * (a * t) := by
      have := h2 y
      rw [hw0sq, hsq] at this
      calc A.sqn L w y ≤ C2 * (a + a * ‖A.zmap w0 s y‖ ^ 2) := this
        _ = C2 * (a * t) := by rw [ht]; ring
        _ ≤ |C2| * (a * t) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    calc A.nsq (m • L) Nsec y ≤ C1 * A.sqn L w y ^ m := h1 y
      _ ≤ max C1 0 * A.sqn L w y ^ m :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hsqw m)
      _ ≤ max C1 0 * (|C2| * (a * t)) ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsqw hb m) (le_max_right _ _)
      _ = (max C1 0 * |C2| ^ m * t ^ m) * a ^ m := by ring
  have hle' : ‖U‖ ^ 2 ≤ max C1 0 * |C2| ^ m * t ^ m :=
    le_of_mul_le_mul_right hle (pow_pos ha0 m)
  have hK : 0 ≤ max C1 0 * |C2| ^ m := by positivity
  calc ‖U‖ = Real.sqrt (‖U‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (max C1 0 * |C2| ^ m * t ^ m) := Real.sqrt_le_sqrt hle'
    _ = Real.sqrt (max C1 0 * |C2| ^ m) * Real.sqrt (t ^ m) :=
        Real.sqrt_mul hK _
    _ = Real.sqrt (max C1 0 * |C2| ^ m) * t ^ ((m : ℝ) / 2) := by
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
        congr 1; ring
end ReciprocityTheory.L2DbarEstimates.Y
