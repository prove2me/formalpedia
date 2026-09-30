-- Prove2me | solution 1 for Verlinde2016.milgrom_relation_point_mass
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:00:36.201198+00:00
-- url     : https://prove2.me/submissions/3d4fdaa5-68f2-408f-9934-2604300a3e0a

import Definitions.Def_Verlinde2016_Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
open Verlinde2016 Real MeasureTheory Filter
open scoped Topology

private theorem avg_deriv (M : ℝ → ℝ) (r v : ℝ) (hr : 0 < r) (hM : HasDerivAt M v r) :
    HasDerivAt (avgDensity M) ((3*v*(4*π*r^3)-3*M r*(4*π*(3*r^2)))/(4*π*r^3)^2) r := by
  have hd := (hM.const_mul 3).div (((hasDerivAt_id r).pow 3).const_mul (4*π)) (by change 4*π*r^3 ≠ 0; positivity)
  convert! hd using 1 <;> simp [avgDensity]

private theorem integral_relation_deriv (G a₀ : ℝ) (ha₀ : 0 < a₀)
    (M_B M_D : ℝ → ℝ) (hM_B_pos : ∀ r : ℝ, 0 < r → 0 < M_B r)
    (hM_D_cont : ContinuousOn M_D (Set.Ioi 0))
    (hmain : ∀ r : ℝ, 0 < r → ∫ s in (0:ℝ)..r, G*M_D s^2/s^2 = M_B r*a₀*r/6)
    (r v : ℝ) (hr : 0 < r) (hM : HasDerivAt M_B v r) :
    G*M_D r^2/r^2 = (v*a₀*r+M_B r*a₀)/6 := by
  have hc : ContinuousOn (fun s => G*M_D s^2/s^2) (Set.Ioi 0) := by
    apply (continuousOn_const.mul (hM_D_cont.pow 2)).div (continuousOn_id.pow 2)
    intro x hx
    exact pow_ne_zero 2 (ne_of_gt hx)
  have hint : IntervalIntegrable (fun s => G*M_D s^2/s^2) volume 0 r := by
    apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
    rw [hmain r hr]
    have hMr := hM_B_pos r hr
    exact ne_of_gt (by positivity)
  have hFTC := intervalIntegral.integral_hasDerivAt_right hint
    (hc.stronglyMeasurableAtFilter isOpen_Ioi r hr) (hc.continuousAt (Ioi_mem_nhds hr))
  have hR : HasDerivAt (fun s => M_B s*a₀*s/6) (G*M_D r^2/r^2) r := hFTC.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact (hmain s hs).symm)
  have hd := ((hM.mul_const a₀).mul (hasDerivAt_id r)).div_const 6
  simpa only [mul_one,id_eq] using hR.unique hd

theorem solution (G a₀ M_B : ℝ) (hG : 0 < G) (ha₀ : 0 < a₀) (hM_B : 0 < M_B)
    (M_D : ℝ → ℝ) (hM_D_cont : ContinuousOn M_D (Set.Ioi 0))
    (hM_D_nonneg : ∀ r : ℝ, 0 < r → 0 ≤ M_D r)
    (hmain : ∀ r : ℝ, 0 < r → ∫ s in (0 : ℝ)..r, G * M_D s ^ 2 / s ^ 2 = M_B * a₀ * r / 6) :
    ∀ r : ℝ, 0 < r → G * M_D r / r ^ 2 = Real.sqrt (a₀ / 6 * (G * M_B / r ^ 2)) := by
  intro r hr
  have hh := integral_relation_deriv G a₀ ha₀ (fun _ => M_B) M_D (fun _ _ => hM_B) hM_D_cont hmain r 0 hr (hasDerivAt_const r M_B)
  have he : (G*M_D r/r^2)^2 = a₀/6*(G*M_B/r^2) := by
    have hh' := congrArg (fun z => G*z/r^2) hh
    convert! hh' using 1 <;> field_simp <;> ring
  apply Eq.symm
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (mul_nonneg hG.le (hM_D_nonneg r hr)) (sq_nonneg r))).mpr
  exact he.symm
