-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.inner_dOp_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:57.051838+00:00
-- url     : https://prove2.me/submissions/9f39881a-07c5-4cf1-9d5a-b2beb45ee2cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {E cp cm : Fin n → Fin n → Module.End ℂ W}
    (hU : IsInfUnitary ε E) (hEC : CommutesCAR E cp cm)
    (hadj : ∀ (i a : Fin n) (x y : W), inner ℂ (cp i a x) y = inner ℂ x (cm i a y)) (x y : W) :
    inner ℂ (dOp ε E cp x) y = inner ℂ x (dOp' ε E cm y) := by
  unfold dOp dOp'
  simp only [LinearMap.sum_apply, LinearMap.neg_apply, sum_inner, inner_neg_right, inner_sum,
    ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => sum_congr rfl fun a ha => ?_
  simp only [plusIdx, minusIdx, mem_filter, mem_univ, true_and] at hi ha
  have hc := LinearMap.congr_fun (hEC i a i a).2 y
  simp only [Module.End.mul_apply] at hc ⊢
  rw [hU, hadj, ← hc]
  simp [adjSign, hi, ha]
end ReciprocityTheory.ChartRestriction.DS
