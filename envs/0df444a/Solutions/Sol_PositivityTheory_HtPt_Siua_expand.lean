-- Prove2me | solution 1 for PositivityTheory.HtPt.Siua.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:30:40.976446+00:00
-- url     : https://prove2.me/submissions/3e9fa129-e5db-441c-898f-70fca4ca4224

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
    (x y : Fin n → ℤ) :
    f (fun i => x i • μ + y i • e) =
      ∑ s : Finset (Fin n), (∏ i, if i ∈ s then x i else y i) * f (fun i => if i ∈ s then μ else e) := by
  have hsum := f.map_add_univ (fun i => x i • μ) (fun i => y i • e)
  rw [show (fun i => x i • μ + y i • e) = (fun i => x i • μ) + (fun i => y i • e) from rfl, hsum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpw : s.piecewise (fun i => x i • μ) (fun i => y i • e) =
      fun i => (if i ∈ s then x i else y i) • (if i ∈ s then μ else e) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [hpw, f.map_smul_univ, smul_eq_mul]
end PositivityTheory.HtPt.Siua
