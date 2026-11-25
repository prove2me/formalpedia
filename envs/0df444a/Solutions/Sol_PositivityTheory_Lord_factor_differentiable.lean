-- Prove2me | solution 1 for PositivityTheory.Lord.factor_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:31:45.365462+00:00
-- url     : https://prove2.me/submissions/b32d8a92-667c-4aca-92d8-e962357a77ea

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_FactorDifferentiable
import Theorems.Thm_PositivityTheory_Lord_PO_mul
import Theorems.Thm_PositivityTheory_Lord_ZO_mul


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
theorem _root_.solution (N : ℕ) (hN : N ≠ 0) (c : ℂ) :
    Differentiable ℂ (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) := by
  intro s
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  exact (differentiableAt_const _).sub
    ((differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hN')))
end PositivityTheory.Lord
