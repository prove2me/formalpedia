-- Prove2me | solution 1 for PositivityTheory.Lord.factor_zo_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:27.434518+00:00
-- url     : https://prove2.me/submissions/e589ca91-67db-4509-8d28-8cc924d47ae2

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_FactorDifferentiable
import Theorems.Thm_PositivityTheory_Lord_factor_analytic
import Theorems.Thm_PositivityTheory_Lord_ZO_one_of_deriv


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
theorem _root_.solution (N : ℕ) (hN : 2 ≤ N) : ZO (fun s : ℂ => 1 - (N : ℂ) ^ (-s)) 0 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have han : AnalyticAt ℂ (fun s : ℂ => 1 - (N : ℂ) ^ (-s)) 0 := by
    simpa only [one_mul] using PositivityTheory.Lord.factor_analytic N (by omega) 1 0
  have hd : HasDerivAt (fun s : ℂ => 1 - (N : ℂ) ^ (-s))
      (-((N : ℂ) ^ (-(0 : ℂ)) * Complex.log N * (-1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).neg).const_cpow (Or.inl hN')).const_sub 1
  refine PositivityTheory.Lord.ZO.one_of_deriv han ?_ ?_
  · show 1 - (N : ℂ) ^ (-(0 : ℂ)) = 0
    rw [neg_zero, Complex.cpow_zero, sub_self]
  · rw [hd.deriv, neg_zero, Complex.cpow_zero, one_mul, mul_neg_one, neg_neg]
    intro hlog
    have h1 : (N : ℂ) = 1 := by rw [← Complex.exp_log hN', hlog, Complex.exp_zero]
    have : N = 1 := by exact_mod_cast h1
    omega
end PositivityTheory.Lord
