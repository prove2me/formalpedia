-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.opsSeq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:20.84832+00:00
-- url     : https://prove2.me/submissions/d5f55995-0e81-472f-93ed-0feda7c32dac

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_Bridge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (s : ℂ) (m : ℕ) : ∀ (k : ℕ) (dirs : Fin k → Fin n × Fin n) (Q : Fm n),
    opsSeq s m k dirs Q = (List.finRange k).foldr (fun i g => opD s m (dirs i).1 (dirs i).2 ∘ₗ g) LinearMap.id Q
  | 0, dirs, Q => by simp [opsSeq]
  | k + 1, dirs, Q => by
    rw [opsSeq, solution s m k (Fin.tail dirs) Q, List.finRange_succ, List.foldr_cons, List.foldr_map]
    rfl
end PositivityTheory.Rg.Sw.SP
