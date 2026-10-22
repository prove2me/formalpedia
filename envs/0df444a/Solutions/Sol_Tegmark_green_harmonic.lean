-- Prove2me | solution 1 for Tegmark.green_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:13:32.287997+00:00
-- url     : https://prove2.me/submissions/42219494-dfdb-408f-92cd-044f1e79fa78

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble
open Tegmark

theorem g71t_green_d1 (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (greenProfile n) ((2 - (n:ℝ)) * x ^ (2 - (n:ℝ) - 1)) x := by
  unfold greenProfile
  exact Real.hasDerivAt_rpow_const (Or.inl hx.ne')

theorem solution (n : ℕ) (_hn : 3 ≤ n) (r : ℝ) (_hr : 0 < r) :
    radialLap n (greenProfile n) r = 0 := by
  have he : (fun x => deriv (greenProfile n) x) =ᶠ[nhds r]
      fun x => (2 - (n:ℝ)) * x ^ (2 - (n:ℝ) - 1) := by
    filter_upwards [lt_mem_nhds _hr] with x hx
    exact (g71t_green_d1 n x hx).deriv
  have h2 : deriv (fun x => deriv (greenProfile n) x) r
      = (2 - (n:ℝ)) * ((2 - (n:ℝ) - 1) * r ^ (2 - (n:ℝ) - 1 - 1)) := by
    rw [he.deriv_eq]
    exact ((Real.hasDerivAt_rpow_const (p := 2 - (n:ℝ) - 1) (Or.inl _hr.ne')).const_mul _).deriv
  unfold radialLap
  rw [h2, (g71t_green_d1 n r _hr).deriv, Real.rpow_sub_one _hr.ne', Real.rpow_sub_one _hr.ne']
  field_simp
  ring
