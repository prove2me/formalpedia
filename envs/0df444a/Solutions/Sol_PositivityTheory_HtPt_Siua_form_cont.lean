-- Prove2me | solution 1 for PositivityTheory.HtPt.Siua.form_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:25:32.529882+00:00
-- url     : https://prove2.me/submissions/b749ae48-6602-492b-99fa-336cbf13fc3c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_SiuaNum

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
    (x : Fin n → ℚ) (y : Fin n → ℚ) : Continuous fun t : ℚ => form f μ e x (fun i => y i * t) := by
  simp only [PositivityTheory.HtPt.Siua.form]
  refine continuous_finsetSum _ fun s _ => ?_
  refine Continuous.mul (continuous_finsetProd _ fun i _ => ?_) continuous_const
  by_cases hi : i ∈ s
  · simp only [hi, ↓reduceIte]
    exact continuous_const
  · simp only [hi, ↓reduceIte]
    exact continuous_const.mul continuous_id
end PositivityTheory.HtPt.Siua
