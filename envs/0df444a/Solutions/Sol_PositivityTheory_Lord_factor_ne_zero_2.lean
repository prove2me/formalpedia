-- Prove2me | solution 2 for PositivityTheory.Lord.factor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:20:46.681613+00:00
-- url     : https://prove2.me/submissions/fbea647e-227c-4722-aaec-a1cd203f9273

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
theorem _root_.solution (N : ℕ) (hN : 2 ≤ N) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 0 < s.re) :
    1 - c * (N : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hpos : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlt : ‖(N : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hN1 (neg_neg_of_pos hs)
  have h1 : c * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖c * (N : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖c‖ * ‖(N : ℂ) ^ (-s)‖ ≤ 1 * ‖(N : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < 1 := by rwa [one_mul]
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn
end PositivityTheory.Lord
