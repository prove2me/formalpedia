-- Prove2me | solution 1 for PositivityTheory.Lord.PO.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:20.345572+00:00
-- url     : https://prove2.me/submissions/e50f3d3f-1aa7-45ec-a60f-06fc1a35d5a2

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
theorem _root_.solution (hf : PO f x k) (h : ∀ᶠ s in 𝓝[≠] x, f s = g s) : PO g x k := by
  obtain ⟨H, hH, hev⟩ := hf
  refine ⟨H, hH, ?_⟩
  filter_upwards [hev, h] with s h1 h2
  rw [h1, h2]
end PO
end PositivityTheory.Lord
