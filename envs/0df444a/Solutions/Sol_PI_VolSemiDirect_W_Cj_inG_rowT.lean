-- Prove2me | solution 1 for PI.VolSemiDirect.W.Cj.inG_rowT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:49.189947+00:00
-- url     : https://prove2.me/submissions/1e7795a6-6c9b-4d1a-bcc3-57a19f501701

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_GlGeneratedTransvectionsDiag
import Theorems.Thm_PI_VolSemiDirect_W_Cj_inG_one
import Theorems.Thm_PI_VolSemiDirect_W_Cj_inG_mul
import Theorems.Thm_PI_VolSemiDirect_W_Cj_inG_transvection

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
theorem _root_.solution (p : Fin k) (c : Fin k → A) (s : Finset (Fin k)) (hp : p ∉ s) :
    InG (1 + ∑ i ∈ s, single p i (c i)) := by
  revert hp
  refine Finset.induction_on s (fun _ => ?_) (fun a t ha ih hp => ?_)
  · rw [Finset.sum_empty, add_zero]
    exact inG_one
  · have hpa : p ≠ a := fun h => hp (by rw [h]; exact Finset.mem_insert_self a t)
    have hpt : p ∉ t := fun h => hp (Finset.mem_insert_of_mem h)
    rw [Finset.sum_insert ha]
    have e : (1 : Matrix (Fin k) (Fin k) A) + (single p a (c a) + ∑ i ∈ t, single p i (c i)) =
        transvection p a (c a) * (1 + ∑ i ∈ t, single p i (c i)) := by
      rw [transvection, add_mul, one_mul, mul_add, mul_one, Finset.mul_sum,
        Finset.sum_eq_zero (fun i _ => single_mul_single_of_ne (c a) p a p (Ne.symm hpa) (c i)),
        add_zero]
      abel
    rw [e]
    exact inG_mul (inG_transvection hpa (c a)) (ih hpt)
end PI.VolSemiDirect.W.Cj
