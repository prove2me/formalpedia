-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P18.appendix_scalar_comparison
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T15:44:09.549231+00:00
-- url     : https://prove2.me/submissions/921bf0e3-4dea-414f-8dc3-74fe17fe57eb

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

open Filter Set Topology
noncomputable section
set_option autoImplicit false

namespace Prove2MeGaussianScalar

private def fOne (x : ℝ) : ℝ := Real.log x
private def fTwo (x : ℝ) : ℝ :=
  ((x + 1) / 2) * Real.log ((x + 1) / 2) -
    ((x - 1) / 2) * Real.log ((x - 1) / 2)

private def slope (x : ℝ) : ℝ := (Real.log (x + 1) - Real.log (x - 1)) / 2

private lemma fTwo_derivative {x : ℝ} (hx : 1 < x) :
    HasDerivAt fTwo (slope x) x := by
  have hp : x + 1 ≠ 0 := by linarith
  have hm : x - 1 ≠ 0 := by linarith
  have ha := (Real.hasDerivAt_mul_log (x := (x + 1) / 2) (div_ne_zero hp (by norm_num))).comp x
    (((hasDerivAt_id x).add_const 1).div_const 2)
  have hb := (Real.hasDerivAt_mul_log (x := (x - 1) / 2) (div_ne_zero hm (by norm_num))).comp x
    (((hasDerivAt_id x).sub_const 1).div_const 2)
  have hd := ha.sub hb
  have heq : (Real.log ((x + 1) / 2) + 1) * (1 / 2) -
      (Real.log ((x - 1) / 2) + 1) * (1 / 2) = slope x := by
    dsimp [slope]
    rw [Real.log_div hp (by norm_num), Real.log_div hm (by norm_num)]
    ring
  rw [heq] at hd
  exact hd

private lemma slope_derivative {x : ℝ} (hx : 1 < x) :
    HasDerivAt slope (-1 / (x ^ 2 - 1)) x := by
  have hp : x + 1 ≠ 0 := by linarith
  have hm : x - 1 ≠ 0 := by linarith
  have hsq : x ^ 2 - 1 ≠ 0 := by nlinarith
  have ha := ((hasDerivAt_id x).add_const 1).log hp
  have hb := ((hasDerivAt_id x).sub_const 1).log hm
  have hd := (ha.sub hb).div_const 2
  have heq : (1 / (x + 1) - 1 / (x - 1)) / 2 = -1 / (x ^ 2 - 1) := by
    field_simp
    ring
  change HasDerivAt slope ((1 / (x + 1) - 1 / (x - 1)) / 2) x at hd
  rw [heq] at hd
  exact hd

private lemma fOne_second {x : ℝ} (hx : 1 < x) :
    deriv (deriv fOne) x = -1 / x ^ 2 := by
  change deriv (deriv Real.log) x = _
  rw [Real.deriv_log']
  convert (hasDerivAt_inv (show x ≠ 0 by linarith)).deriv using 1 <;> ring

private lemma fTwo_second {x : ℝ} (hx : 1 < x) :
    deriv (deriv fTwo) x = -1 / (x ^ 2 - 1) := by
  apply HasDerivAt.deriv
  apply (slope_derivative hx).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact (fTwo_derivative hy).deriv

private lemma second_comparison {x : ℝ} (hx : 1 < x) :
    deriv (deriv fTwo) x < deriv (deriv fOne) x := by
  rw [fTwo_second hx, fOne_second hx]
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos (by linarith)
  have hd : 0 < x ^ 2 - 1 := by nlinarith
  apply (div_lt_div_iff₀ hd hx2).2
  nlinarith

private lemma slope_limit : Tendsto slope atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => (x - 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  have hratio : Tendsto (fun x : ℝ => 1 + 2 * (x - 1)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hlim : Tendsto (fun x : ℝ => Real.log (1 + 2 * (x - 1)⁻¹) / 2)
      atTop (𝓝 0) := by simpa using hlog.div_const 2
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hp : x + 1 ≠ 0 := by linarith
  have hm : x - 1 ≠ 0 := by linarith
  have hid : 1 + 2 * (x - 1)⁻¹ = (x + 1) / (x - 1) := by
    field_simp
    ring
  rw [hid, Real.log_div hp hm]
  rfl

private lemma slope_gt_inv {x : ℝ} (hx : 1 < x) : x⁻¹ < slope x := by
  let d : ℝ → ℝ := fun y => slope y - y⁻¹
  have hd (y : ℝ) (hy : 1 < y) :
      HasDerivAt d (-1 / (y ^ 2 - 1) - -(y ^ 2)⁻¹) y := by
    exact (slope_derivative hy).sub (hasDerivAt_inv (by linarith))
  have hneg (y : ℝ) (hy : 1 < y) : deriv d y < 0 := by
    rw [(hd y hy).deriv]
    have h := second_comparison hy
    rw [fTwo_second hy, fOne_second hy] at h
    simpa only [neg_div, one_div, sub_neg_eq_add] using sub_neg.mpr h
  have hanti : StrictAntiOn d (Ioi 1) :=
    strictAntiOn_of_deriv_neg (convex_Ioi 1)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => hneg y (by simpa using hy))
  have hlim : Tendsto d atTop (𝓝 0) := by
    simpa [d] using slope_limit.sub tendsto_inv_atTop_zero
  have hnonneg (y : ℝ) (hy : 1 < y) : 0 ≤ d y := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop y] with z hz
    exact hanti.antitoneOn hy (lt_of_lt_of_le hy hz) hz
  have hstrict := hanti hx (show 1 < x + 1 by linarith) (by linarith : x < x + 1)
  have hn := hnonneg (x + 1) (by linarith)
  dsimp [d] at hstrict hn
  linarith

private lemma function_comparison {x : ℝ} (hx : 1 < x) : fOne x < fTwo x := by
  have hc2 : Continuous fTwo := by
    exact (Real.continuous_mul_log.comp ((continuous_id.add continuous_const).div_const 2)).sub
      (Real.continuous_mul_log.comp ((continuous_id.sub continuous_const).div_const 2))
  have hc1 : ContinuousOn fOne (Ici 1) := by
    intro y hy
    exact (Real.continuousAt_log (by change 1 ≤ y at hy; linarith)).continuousWithinAt
  have hmono : StrictMonoOn (fun y => fTwo y - fOne y) (Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1) (hc2.continuousOn.sub hc1)
    intro y hy
    have hy' : 1 < y := by simpa using hy
    have hd := (fTwo_derivative hy').sub (Real.hasDerivAt_log (by linarith : y ≠ 0))
    change 0 < deriv (fTwo - Real.log) y
    rw [hd.deriv]
    exact sub_pos.mpr (slope_gt_inv hy')
  have h := hmono (show (1 : ℝ) ∈ Ici 1 by simp) (le_of_lt hx) hx
  norm_num [fOne, fTwo] at h
  exact h

end Prove2MeGaussianScalar

open Prove2MeGaussianScalar

theorem solution :
    fOne 1 = fTwo 1 ∧
    Tendsto (deriv fOne) atTop (𝓝 0) ∧ Tendsto (deriv fTwo) atTop (𝓝 0) ∧
    (∀ x : ℝ, 1 < x → deriv (deriv fTwo) x < deriv (deriv fOne) x) ∧
    (∀ x : ℝ, 1 < x → fOne x < fTwo x) := by
  refine ⟨by norm_num [fOne, fTwo], ?_, ?_, fun _ hx => second_comparison hx,
    fun _ hx => function_comparison hx⟩
  · change Tendsto (deriv Real.log) atTop (𝓝 0)
    rw [Real.deriv_log']
    exact tendsto_inv_atTop_zero
  · apply slope_limit.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (fTwo_derivative hx).deriv.symm
