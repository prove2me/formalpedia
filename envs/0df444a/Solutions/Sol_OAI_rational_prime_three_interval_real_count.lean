-- Prove2me | solution 1 for OAI.rational_prime_three_interval_real_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:30.594822+00:00
-- url     : https://prove2.me/submissions/154c6c10-46fa-4a32-8c74-e6f9e45e2a41

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace OscillatoryDeterminant
open Complex
end OscillatoryDeterminant
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace EisensteinFiberShift
end EisensteinFiberShift
namespace ShortDraftLatticeCount
open ActualEisensteinCoordinates
end ShortDraftLatticeCount
namespace EisensteinGaussianPrefactor
end EisensteinGaussianPrefactor
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace EisensteinGaussianPrefactor
end EisensteinGaussianPrefactor
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace OscillatoryDeterminant
open Complex
end OscillatoryDeterminant
open Filter Real Asymptotics
private theorem cheby_small_log :
    ∀ᶠ Y : ℝ in atTop, Real.log (Y + 2) ≤ (Real.log 2 / 80) * (Y + 2) := by
  have hsmall : (fun x : ℝ => Real.log x) =o[atTop] id := by
    simpa only [pow_one] using (Real.isLittleO_pow_log_id_atTop (n := 1))
  have hbound := hsmall.bound (by positivity : 0 < Real.log (2 : ℝ) / 80)
  have hshift : Tendsto (fun Y : ℝ => Y + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  filter_upwards [hshift.eventually hbound,
    eventually_ge_atTop (1 : ℝ)] with Y hY hY1
  simpa only [Function.comp_def, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ Y + 2)),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ Y + 2)] using hY
namespace RankTwoLimit
section
open scoped Topology
open RankTwoPoisson RankTwoEisShift Filter
end
open scoped Topology
open Filter
end RankTwoLimit
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
namespace OAI
theorem _root_.solution :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((Real.log 2) / 20) * (Y / Real.log Y) ≤
        (Nat.primeCounting ⌊Y⌋₊ : ℝ) -
          (Nat.primeCounting ⌊Y / 3⌋₊ : ℝ) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hε : 0 < Real.log (2 : ℝ) / 4 := by positivity
  obtain ⟨X₀, hX₀⟩ := (eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le hε))
  obtain ⟨X₁, hX₁⟩ := (eventually_atTop.1 cheby_small_log)
  refine ⟨max 729 (max (3 * X₀) X₁), ?_⟩
  intro Y hY
  have hY729 : (729 : ℝ) ≤ Y := le_trans (le_max_left _ _) hY
  have hYX₀ : X₀ ≤ Y / 3 := by
    linarith [le_max_left (3 * X₀) X₁, le_max_right (729 : ℝ) (max (3 * X₀) X₁)]
  have hYX₁ : X₁ ≤ Y := by
    linarith [le_max_right (3 * X₀) X₁, le_max_right (729 : ℝ) (max (3 * X₀) X₁)]
  have hYpos : (0 : ℝ) < Y := by linarith
  have hY3pos : (0 : ℝ) < Y / 3 := by positivity
  have hlogYpos : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogY3pos : 0 < Real.log (Y / 3) := Real.log_pos (by linarith)
  have hlog3 : 6 * Real.log (3 : ℝ) ≤ Real.log Y := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 729) hY729
    calc
      6 * Real.log (3 : ℝ) = Real.log ((3 : ℝ) ^ 6) := by rw [Real.log_pow]; ring
      _ = Real.log 729 := by norm_num
      _ ≤ Real.log Y := h
  have hlogY3 : 5 / 6 * Real.log Y ≤ Real.log (Y / 3) := by
    rw [Real.log_div (ne_of_gt hYpos) (by norm_num : (3 : ℝ) ≠ 0)]
    linarith
  have hlogerror : Real.log (Y + 2) ≤ (Real.log 2 / 40) * Y := by
    have hbound := hX₁ Y hYX₁
    have hprod : 0 ≤ Real.log 2 * (Y - 2) :=
      mul_nonneg hlog2pos.le (by linarith)
    nlinarith
  have hconsterror : Real.log (2 : ℝ) ≤ (Real.log 2 / 40) * Y := by
    have hprod : 0 ≤ Real.log 2 * (Y - 40) :=
      mul_nonneg hlog2pos.le (by linarith)
    nlinarith
  have hnumlo : (19 / 20 : ℝ) * Real.log 2 * Y ≤
      (Y - 1) * Real.log 2 - Real.log (Y + 2) := by
    nlinarith [hlogerror, hconsterror]
  have hPlo : (19 / 20 : ℝ) * Real.log 2 * (Y / Real.log Y) ≤
      (Nat.primeCounting ⌊Y⌋₊ : ℝ) := by
    calc
      _ = ((19 / 20 : ℝ) * Real.log 2 * Y) / Real.log Y := by ring
      _ ≤ ((Y - 1) * Real.log 2 - Real.log (Y + 2)) / Real.log Y :=
        (div_le_div_of_nonneg_right hnumlo hlogYpos.le)
      _ ≤ _ := Chebyshev.pi_ge' (by linarith)
  have hfrac : (Y / 3) / Real.log (Y / 3) ≤ (2 / 5 : ℝ) * (Y / Real.log Y) := by
    have hprod : 0 ≤ Y * (Real.log (Y / 3) - 5 / 6 * Real.log Y) :=
      mul_nonneg hYpos.le (sub_nonneg.mpr hlogY3)
    have hq : (Y / 3) / Real.log (Y / 3) ≤
        ((2 / 5 : ℝ) * Y) / Real.log Y := by
      apply (div_le_div_iff₀ hlogY3pos hlogYpos).mpr
      nlinarith
    convert hq using 1 ; ring
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; ring
  have hcoeff : 0 ≤ Real.log 4 + Real.log 2 / 4 := by positivity
  have hPup : (Nat.primeCounting ⌊Y / 3⌋₊ : ℝ) ≤
      (9 / 10 : ℝ) * Real.log 2 * (Y / Real.log Y) := by
    calc
      _ ≤ (Real.log 4 + Real.log 2 / 4) * ((Y / 3) / Real.log (Y / 3)) :=
        by simpa only [mul_div_assoc] using hX₀ (Y / 3) hYX₀
      _ ≤ (Real.log 4 + Real.log 2 / 4) * ((2 / 5 : ℝ) * (Y / Real.log Y)) :=
        mul_le_mul_of_nonneg_left hfrac hcoeff
      _ = (9 / 10 : ℝ) * Real.log 2 * (Y / Real.log Y) := by rw [hlog4]; ring
  have htarget : (Real.log 2 / 20) * (Y / Real.log Y) =
      ((19 / 20 : ℝ) - 9 / 10) * Real.log 2 * (Y / Real.log Y) := by ring
  rw [htarget]
  linarith
end OAI
