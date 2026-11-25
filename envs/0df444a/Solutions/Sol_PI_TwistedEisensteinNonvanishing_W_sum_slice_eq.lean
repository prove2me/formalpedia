-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.sum_slice_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:15.46311+00:00
-- url     : https://prove2.me/submissions/807d352a-7062-43fe-adbe-98285ff90665

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sum_slice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (k : ι) (S : ι → Finset E) (T T' : Finset E) (F G : (ι → E) → K) (α : K)
    (h : ∀ t : ι → E, ∑ u ∈ T, F (update t k u) = α * ∑ u ∈ T', G (update t k u)) :
    ∑ t ∈ Fintype.piFinset (update S k T), F t = α * ∑ t ∈ Fintype.piFinset (update S k T'), G t := by
  rw [sum_slice k (update S k T) 0 F, sum_slice k (update S k T') 0 G]
  simp only [Function.update_idem, Function.update_self]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => h t
end PI.TwistedEisensteinNonvanishing.W
