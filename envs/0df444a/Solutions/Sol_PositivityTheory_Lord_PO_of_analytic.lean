-- Prove2me | solution 1 for PositivityTheory.Lord.PO.of_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:54.511173+00:00
-- url     : https://prove2.me/submissions/f71685c2-5d45-4926-a510-80b79341f712

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
namespace PO
theorem _root_.solution (hf : AnalyticAt ℂ f x) : PO f x 0 :=
  ⟨f, hf, Filter.Eventually.of_forall fun s => by rw [pow_zero, one_mul]⟩
end PO
end PositivityTheory.Lord
