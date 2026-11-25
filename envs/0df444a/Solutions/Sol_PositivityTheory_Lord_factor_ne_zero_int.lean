-- Prove2me | solution 1 for PositivityTheory.Lord.factor_ne_zero_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:31:48.190429+00:00
-- url     : https://prove2.me/submissions/9af85242-15b6-42d5-bd53-eb6282d42851

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_FactorDifferentiable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex NumberField IsDedekindDomain
open PositivityTheory PositivityTheory.Lord
namespace PositivityTheory.Lord
theorem _root_.solution (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ = 1) (j : ℤ) (hj : j ≠ 0) :
    1 - c * (N : ℂ) ^ (-(j : ℂ)) ≠ 0 := by
  intro h
  have hpos : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have h1 : c * (N : ℂ) ^ (-(j : ℂ)) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖c * (N : ℂ) ^ (-(j : ℂ))‖ = ‖(1 : ℂ)‖ := by rw [h1]
  rw [norm_mul, hc, one_mul, norm_one, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re,
    Complex.intCast_re] at hn
  rcases lt_or_gt_of_ne hj with hj' | hj'
  · have hjr : (j : ℝ) < 0 := by exact_mod_cast hj'
    have : (1 : ℝ) < (N : ℝ) ^ (-(j : ℝ)) := Real.one_lt_rpow hN1 (by linarith)
    linarith
  · have hjr : (0 : ℝ) < j := by exact_mod_cast hj'
    have : (N : ℝ) ^ (-(j : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by linarith)
    linarith
end PositivityTheory.Lord
