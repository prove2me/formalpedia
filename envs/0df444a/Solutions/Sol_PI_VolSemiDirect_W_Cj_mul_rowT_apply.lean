-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.mul_rowT_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:49:08.091747+00:00
-- url     : https://prove2.me/submissions/656b87ad-b690-4084-baf7-370fd60f8175

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.Cj
open Matrix
variable {A : Type} [CommRing A] {k : ℕ}
namespace PI.VolSemiDirect.W.Cj
theorem _root_.solution (p : Fin k) (c : Fin k → A) (s : Finset (Fin k))
    (X : Matrix (Fin k) (Fin k) A) (a b : Fin k) :
    (X * (1 + ∑ j ∈ s, single p j (c j))) a b =
      X a b + if b ∈ s then X a p * c b else 0 := by
  rw [mul_add, mul_one, Finset.mul_sum, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  split_ifs with hb
  · rw [Finset.sum_eq_single b]
    · exact mul_single_apply_same _ _ _ _ _
    · intro j _ hjb
      exact mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hjb) _
    · intro h
      exact absurd hb h
  · exact Finset.sum_eq_zero (fun j hj => mul_single_apply_of_ne _ _ _ _ _
      (fun h => hb (by rw [h]; exact hj)) _)
end PI.VolSemiDirect.W.Cj
