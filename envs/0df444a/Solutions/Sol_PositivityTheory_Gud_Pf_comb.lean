-- Prove2me | solution 1 for PositivityTheory.Gud.Pf.comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:44.295347+00:00
-- url     : https://prove2.me/submissions/6240b353-1163-4e39-b866-62efb148b1e6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitaryDualGL_GenericUnitaryDual_PComb
import Theorems.Thm_PositivityTheory_Gud_Pf_list_symmetric_pair_decomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Gud PositivityTheory.Gud.Pf
namespace PositivityTheory.Gud.Pf
theorem _root_.solution {α : Type*} (l : List (α × ℝ)) (hl : List.Perm (l.map (fun p => (p.1, -p.2))) l) :
    ∃ (a : List α) (b : List (α × ℝ)), (∀ p ∈ b, 0 < p.2 ∧ p ∈ l) ∧
      List.Perm (a.map (fun x => (x, (0 : ℝ))) ++ b.flatMap (fun p => [p, (p.1, -p.2)])) l := list_symmetric_pair_decomposition l.length l rfl hl
end PositivityTheory.Gud.Pf
