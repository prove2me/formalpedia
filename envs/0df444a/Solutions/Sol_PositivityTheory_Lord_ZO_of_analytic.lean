-- Prove2me | solution 1 for PositivityTheory.Lord.ZO.of_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:48.635089+00:00
-- url     : https://prove2.me/submissions/56fb3a3a-8b6e-4bf9-94c4-b656b03e6094

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open PositivityTheory PositivityTheory.Lord
variable {f g : ℂ → ℂ} {x : ℂ} {k l m n : ℕ}
namespace PositivityTheory.Lord
namespace ZO
theorem _root_.solution (hf : AnalyticAt ℂ f x) (h0 : f x ≠ 0) : ZO f x 0 :=
  ⟨f, hf, h0, Filter.Eventually.of_forall fun s => by rw [pow_zero, one_mul]⟩
end ZO
end PositivityTheory.Lord
