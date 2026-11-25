-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_FinitePlaceSumBound_finitePlace_sum_le__f64df29d0620
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:37.891833+00:00
-- url     : https://prove2.me/submissions/f7e1fd9b-2917-4f09-b77f-7781f409a62d

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FinitePlaceSumLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.FinitePlaceSumBound.finitePlace_sum_le
theorem _root_.solution.{u_1, u_2} :
    ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K] (v : NumberField.FinitePlace K) {α : Type u_2} (s : Finset α)
      (f : α → K) {B : ℝ}, (0 : ℝ) ≤ B → (∀ a ∈ s, (v : K → ℝ) (f a) ≤ B) → (v : K → ℝ) (∑ a ∈ s, f a) ≤ B := by
  intro K _ _ v α s f B hB h
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (NumberField.FinitePlace.add_le v _ _).trans
      (max_le (h a (Finset.mem_insert_self a s))
        (ih fun b hb => h b (Finset.mem_insert_of_mem hb)))
end UpperTheory.Reformulated.B.FinitePlaceSumBound.finitePlace_sum_le
