-- Prove2me | solution 1 for PositivityTheory.ThKEst.W.rank_iff_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:40.821777+00:00
-- url     : https://prove2.me/submissions/78177172-5023-4837-8639-3268c7e6487e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_RankIffRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology GlobalTheory.WeilM
open scoped Pointwise
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.W
variable {k : Type} [Field k] {n d : ℕ}
namespace PositivityTheory.ThKEst.W
theorem _root_.solution (Y : Matrix (Fin n) (Fin d) k) : Y.rank = n ↔ ∃ C : Matrix (Fin d) (Fin n) k, Y * C = 1 := by
  constructor
  · intro h
    have hr : LinearMap.range Y.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      exact h
    have hsurj : Function.Surjective Y.mulVecLin := LinearMap.range_eq_top.mp hr
    choose c hc using fun j : Fin n => hsurj (Pi.single j 1)
    refine ⟨Matrix.of fun a j => c j a, ?_⟩
    ext i j
    have h3 := congrFun (hc j) i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at h3
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [h3, Pi.single_apply]
  · rintro ⟨C, hC⟩
    apply le_antisymm (Matrix.rank_le_height Y)
    calc n = (1 : Matrix (Fin n) (Fin n) k).rank := by rw [Matrix.rank_one, Fintype.card_fin]
      _ = (Y * C).rank := by rw [hC]
      _ ≤ Y.rank := Matrix.rank_mul_le_left Y C
end PositivityTheory.ThKEst.W
