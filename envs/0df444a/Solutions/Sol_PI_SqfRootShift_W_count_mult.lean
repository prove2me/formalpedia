-- Prove2me | solution 1 for PI.SqfRootShift.W.count_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:34:08.946599+00:00
-- url     : https://prove2.me/submissions/53526873-e579-4c6d-9e82-4b1341e625b0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootShift_CountC
import Theorems.Thm_PI_SqfRootShift_W_monic_ext
import Theorems.Thm_PI_SqfRootShift_W_divByMonic_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootShift PI.SqfRootShift.W
open PI.SqfLab
variable {g : ℕ} [Fact g.Prime]
open Classical
namespace PI.SqfRootShift.W
theorem _root_.solution (r : ℕ) (T : Finset (ZMod g)[X]) (hT : ∀ f ∈ T, IsLab g r f)
    (P : (ZMod g)[X]) (hP : P.Monic) :
    (T.filter (fun f => P ∣ f)).card ≤ g ^ (r - P.natDegree) := by
  have hu : (Finset.univ : Finset (Fin (r - P.natDegree) → ZMod g)).card =
      g ^ (r - P.natDegree) := by
    simp [ZMod.card]
  rw [← hu]
  refine Finset.card_le_card_of_injOn (fun f (i : Fin (r - P.natDegree)) => (f /ₘ P).coeff i)
    ?_ ?_
  · intro f _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  · intro f1 hf1 f2 hf2 h
    rw [Finset.mem_coe, Finset.mem_filter] at hf1 hf2
    obtain ⟨e1, m1, d1⟩ := divByMonic_facts (hT f1 hf1.1) hP hf1.2
    obtain ⟨e2, m2, d2⟩ := divByMonic_facts (hT f2 hf2.1) hP hf2.2
    have hq : f1 /ₘ P = f2 /ₘ P := monic_ext m1 m2 d1 d2 (fun i hi => congrFun h ⟨i, hi⟩)
    rw [e1, e2, hq]
end PI.SqfRootShift.W
