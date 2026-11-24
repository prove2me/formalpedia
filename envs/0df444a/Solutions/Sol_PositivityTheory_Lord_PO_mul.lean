-- Prove2me | solution 1 for PositivityTheory.Lord.PO.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:45.176045+00:00
-- url     : https://prove2.me/submissions/5ebd677b-ecdb-45b0-9b15-abc59339847d

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
theorem _root_.solution (hf : PO f x k) (hg : PO g x l) : PO (fun s => f s * g s) x (k + l) := by
  obtain ⟨H, hH, hevH⟩ := hf
  obtain ⟨G, hG, hevG⟩ := hg
  refine ⟨fun s => H s * G s, hH.fun_mul hG, ?_⟩
  filter_upwards [hevH, hevG] with s hs ht
  rw [hs, ht, pow_add]
  ring
end PO
end PositivityTheory.Lord
