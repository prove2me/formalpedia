-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.intw_of_sympl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:26.494442+00:00
-- url     : https://prove2.me/submissions/c015c6bd-eb61-48da-8739-cf7d44a1bc6c

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalLift
import Theorems.Thm_PositivityTheory_ThKR_LL_pPart_mulVec
import Theorems.Thm_PositivityTheory_ThKR_LL_qPart_mulVec
import Theorems.Thm_PositivityTheory_ThKR_LL_intw_big


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {g : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hg : ∀ w w', sympl (g *ᵥ w) (g *ᵥ w') = sympl w w')
    (h : IsUnit (bl Sum.inl Sum.inl g)) (c : ℝ) (w : l ⊕ l → ℝ) :
    Intw (big (Ring.inverse (bl Sum.inl Sum.inl g)) (bl Sum.inl Sum.inr g) (bl Sum.inr Sum.inl g) c) (pPart w) (qPart w)
      (pPart (g *ᵥ w)) (qPart (g *ᵥ w)) := by
  have key : ∀ p q p' q' : Eu l, ⟪bl Sum.inl Sum.inl g p + bl Sum.inl Sum.inr g q,
      bl Sum.inr Sum.inl g p' + bl Sum.inr Sum.inr g q'⟫ - ⟪bl Sum.inr Sum.inl g p + bl Sum.inr Sum.inr g q,
      bl Sum.inl Sum.inl g p' + bl Sum.inl Sum.inr g q'⟫ = ⟪p, q'⟫ - ⟪q, p'⟫ := fun p q p' q' => by
    have := hg (Sum.elim (fun i => p i) fun i => q i) (Sum.elim (fun i => p' i) fun i => q' i)
    simp only [sympl, pPart_mulVec, qPart_mulVec] at this
    exact this
  rw [pPart_mulVec, qPart_mulVec]
  refine intw_big h.ringInverse (fun x => ?_) (fun x => ?_) (fun y z => ?_) (fun y z => ?_) (fun y z => ?_) c _ _
  · rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ h, ContinuousLinearMap.one_apply]
  · rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ h, ContinuousLinearMap.one_apply]
  · simpa [sub_eq_zero] using key y 0 z 0
  · simpa [sub_eq_zero] using key 0 y 0 z
  · simpa using key y 0 0 z
end PositivityTheory.ThKR.LL
