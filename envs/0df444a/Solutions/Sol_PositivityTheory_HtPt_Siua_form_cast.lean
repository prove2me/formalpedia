-- Prove2me | solution 1 for PositivityTheory.HtPt.Siua.form_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:38:26.481395+00:00
-- url     : https://prove2.me/submissions/bbea236a-33ee-4956-ae1a-9597a9fae6ef

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_SiuaNum
import Theorems.Thm_PositivityTheory_HtPt_Siua_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.Siua
open Filter Topology
namespace PositivityTheory.HtPt.Siua
theorem _root_.solution {M : Type} [AddCommGroup M] {n : ℕ} (f : MultilinearMap ℤ (fun _ : Fin n => M) ℤ) (μ e : M)
    (x y : Fin n → ℤ) :
    (f (fun i => x i • μ + y i • e) : ℚ) = form f μ e (fun i => x i) (fun i => y i) := by
  rw [PositivityTheory.HtPt.Siua.expand]
  simp only [PositivityTheory.HtPt.Siua.form]
  push_cast
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
end PositivityTheory.HtPt.Siua
