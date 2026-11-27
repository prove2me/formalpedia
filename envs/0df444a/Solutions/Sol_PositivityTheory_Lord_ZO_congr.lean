-- Prove2me | solution 1 for PositivityTheory.Lord.ZO.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:27.357813+00:00
-- url     : https://prove2.me/submissions/a96ff4dc-cfe7-46e2-b5f3-23c921536801

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
theorem _root_.solution (hf : ZO f x m) (h : ∀ᶠ s in 𝓝[≠] x, f s = g s) : ZO g x m := by
  obtain ⟨u, hu, hux, hev⟩ := hf
  refine ⟨u, hu, hux, ?_⟩
  filter_upwards [hev, h] with s h1 h2
  rw [← h2, h1]
end ZO
end PositivityTheory.Lord
