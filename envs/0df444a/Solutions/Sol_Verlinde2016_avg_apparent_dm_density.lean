-- Prove2me | solution 1 for Verlinde2016.avg_apparent_dm_density
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:01:29.792125+00:00
-- url     : https://prove2.me/submissions/5e86cc8f-0524-4934-829d-2bc297443506

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

theorem solution (G a₀ : ℝ) (hG : 0 < G) (ha₀ : 0 < a₀)
    (M_B M_D : ℝ → ℝ) (hM_B_diff : DifferentiableOn ℝ M_B (Set.Ioi 0))
    (hM_B_pos : ∀ r : ℝ, 0 < r → 0 < M_B r) (hM_D_cont : ContinuousOn M_D (Set.Ioi 0))
    (hmain : ∀ r : ℝ, 0 < r → ∫ s in (0 : ℝ)..r, G * M_D s ^ 2 / s ^ 2 = M_B r * a₀ * r / 6) :
    ∀ r : ℝ, 0 < r → avgDensity M_D r ^ 2
      = (4 - slopeParam (avgDensity M_B) r) * a₀ * avgDensity M_B r / (8 * π * G * r) := by
  intro r hr
  have hMd := (hM_B_diff.differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
  have hh := integral_relation_deriv G a₀ ha₀ M_B M_D hM_B_pos hM_D_cont hmain r (deriv M_B r) hr hMd
  have havg := (avg_deriv M_B r _ hr hMd).deriv
  have he := congrArg (fun z => 9*z/(16*π^2*G*r^4)) hh
  simp only [slopeParam,havg,avgDensity]
  convert! he using 1 <;> field_simp [hr.ne',hG.ne',Real.pi_ne_zero,(hM_B_pos r hr).ne'] <;> ring
