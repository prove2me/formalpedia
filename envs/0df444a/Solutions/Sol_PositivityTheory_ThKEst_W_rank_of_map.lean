-- Prove2me | solution 1 for PositivityTheory.ThKEst.W.rank_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:41.389152+00:00
-- url     : https://prove2.me/submissions/04037440-0983-4515-ac23-71563ed27b88

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
theorem _root_.solution {E : Type} [Field E] (t : E →+* k) (x : Matrix (Fin n) (Fin d) E) (h : (x.map t).rank = n) :
    x.rank = n := by
  rw [← Matrix.rank_transpose] at h ⊢
  have hinj : Function.Injective ((x.map t)ᵀ.mulVecLin) := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker ((x.map t)ᵀ.mulVecLin)
    rw [Module.finrank_fin_fun] at h1
    have h2 : Module.finrank k (LinearMap.range ((x.map t)ᵀ.mulVecLin)) = n := h
    omega
  have hinj2 : Function.Injective (xᵀ.mulVecLin) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h3 : (x.map t)ᵀ.mulVecLin (⇑t ∘ c) = 0 := by
      funext j
      have h4 := congrFun hc j
      simp only [Matrix.mulVecLin_apply, Pi.zero_apply] at h4 ⊢
      rw [← Matrix.transpose_map, ← RingHom.map_mulVec, h4, map_zero]
    have h5 := hinj (h3.trans (map_zero _).symm)
    funext i
    have h6 := congrFun h5 i
    exact (map_eq_zero t).mp h6
  show Module.finrank E (LinearMap.range xᵀ.mulVecLin) = n
  rw [LinearMap.finrank_range_of_inj hinj2, Module.finrank_fin_fun]
end PositivityTheory.ThKEst.W
