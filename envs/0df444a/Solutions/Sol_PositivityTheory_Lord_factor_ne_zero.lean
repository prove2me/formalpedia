-- Prove2me | solution 1 for PositivityTheory.Lord.factor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:37:16.304794+00:00
-- url     : https://prove2.me/submissions/cf9efb9c-a89a-4efa-99da-116fb7a82655

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
theorem _root_.solution (N : ℕ) (hN : 2 ≤ N) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 0 < s.re) :
    1 - c * (N : ℂ) ^ (-s) ≠ 0 := by
  first
    | (intro h
       have h1 : c * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 h).symm
       have h2 : ‖(N : ℂ) ^ (-s)‖ < 1 := by
         rw [Complex.norm_natCast_cpow_of_pos (by omega)]
         refine Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < N)) ?_
         rw [Complex.neg_re]; linarith
       have h3 := congrArg norm h1
       rw [norm_mul, norm_one] at h3
       have := mul_le_mul_of_nonneg_right hc (norm_nonneg ((N : ℂ) ^ (-s)))
       rw [h3, one_mul] at this
       linarith)

