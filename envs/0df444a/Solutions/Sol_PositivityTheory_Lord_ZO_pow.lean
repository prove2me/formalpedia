-- Prove2me | solution 1 for PositivityTheory.Lord.ZO.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:29.310262+00:00
-- url     : https://prove2.me/submissions/88f29824-15d9-4bf9-98a1-1e00ff60ebaf

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
theorem _root_.solution (hf : ZO f x m) (n : ℕ) : ZO (fun s => f s ^ n) x (m * n) := by
  obtain ⟨u, hu, hux, hev⟩ := hf
  refine ⟨fun s => u s ^ n, hu.fun_pow n, pow_ne_zero n hux, ?_⟩
  filter_upwards [hev] with s hs
  rw [hs, mul_pow, pow_mul]
end ZO
end PositivityTheory.Lord
