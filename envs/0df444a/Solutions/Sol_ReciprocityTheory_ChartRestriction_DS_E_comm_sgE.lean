-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.E_comm_sgE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:12:28.150058+00:00
-- url     : https://prove2.me/submissions/bfc113d7-deec-4969-879b-611b4a80a701

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
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E cp cm : Fin n → Fin n → Module.End ℂ W} (hEC : CommutesCAR E cp cm)
    (ε : Fin n → Bool) (a b c d : Fin n) : E a b * sgE ε cp cm c d = sgE ε cp cm c d * E a b := by
  have h1 : ∀ i j k l, E a b * (cp i j * cm k l) = (cp i j * cm k l) * E a b := by
    intro i j k l
    rw [← mul_assoc, (hEC a b i j).1, mul_assoc, (hEC a b k l).2, mul_assoc]
  unfold sgE
  split_ifs
  · rw [mul_sum, sum_mul]; exact sum_congr rfl fun x _ => h1 _ _ _ _
  · rw [mul_neg, neg_mul, mul_sum, sum_mul]; congr 1; exact sum_congr rfl fun x _ => h1 _ _ _ _
  · simp
end ReciprocityTheory.ChartRestriction.DS
