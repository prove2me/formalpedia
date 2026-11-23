-- Prove2me | solution 1 for RiemannVonMangoldt.lindelof_error_littleO
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:51.789506+00:00
-- url     : https://prove2.me/submissions/a1dcb531-add8-4892-9a85-58891f796610
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_RiemannVonMangoldt_riemann_hypothesis_error_bigO

open Filter Asymptotics Real

namespace RiemannVonMangoldt
end RiemannVonMangoldt
open RiemannVonMangoldt
theorem solution (hL : LindelofHypothesis) :
    (fun T : ℝ => zetaZeroCount T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π)))
      =o[atTop] Real.log :=
  by
  have hO := RiemannVonMangoldt.riemann_hypothesis_error_bigO mathlib_riemannHypothesis
  have h1 : Filter.Tendsto (fun T : ℝ => (Real.log (Real.log T))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  have h2 : (fun T : ℝ => (Real.log (Real.log T))⁻¹) =o[Filter.atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr h1
  have h3 : (fun T : ℝ => Real.log T / Real.log (Real.log T)) =o[Filter.atTop] Real.log :=
    ((Asymptotics.isBigO_refl Real.log Filter.atTop).mul_isLittleO h2).congr
      (fun T => (div_eq_mul_inv (Real.log T) (Real.log (Real.log T))).symm)
      (fun T => mul_one (Real.log T))
  exact hO.trans_isLittleO h3
