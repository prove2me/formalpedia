-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.rowT_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:49:13.990047+00:00
-- url     : https://prove2.me/submissions/b4bd1a6d-0d9a-418b-8e9e-487e44116159

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
    ((1 + ∑ i ∈ s, single p i (c i)) * X) a b =
      X a b + if a = p then ∑ i ∈ s, c i * X i b else 0 := by
  rw [add_mul, one_mul, Finset.sum_mul, Matrix.add_apply, Matrix.sum_apply]
  congr 1
  split_ifs with ha
  · subst ha
    exact Finset.sum_congr rfl (fun i _ => single_mul_apply_same _ _ _ _ _)
  · exact Finset.sum_eq_zero (fun i _ => single_mul_apply_of_ne _ _ _ _ _ ha _)
end PI.VolSemiDirect.W.Cj
