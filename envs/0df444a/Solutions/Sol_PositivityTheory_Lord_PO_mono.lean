-- Prove2me | solution 1 for PositivityTheory.Lord.PO.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:22.640434+00:00
-- url     : https://prove2.me/submissions/5d3d7770-60ae-4ae4-9f2d-0a1189a6b061

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
theorem _root_.solution (h : PO f x k) (hk : k ≤ l) : PO f x l := by
  obtain ⟨H, hH, hev⟩ := h
  refine ⟨fun s => (s - x) ^ (l - k) * H s,
    ((analyticAt_id.sub analyticAt_const).fun_pow _).fun_mul hH, ?_⟩
  filter_upwards [hev] with s hs
  rw [hs, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
end PO
end PositivityTheory.Lord
