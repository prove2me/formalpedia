-- Prove2me | solution 1 for PI.RWS.wt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:12:57.012014+00:00
-- url     : https://prove2.me/submissions/407335f3-4db0-4f1d-951f-dc30af263218

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowWtSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowWeightSpan_RowWtSpanOfBideterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.RWS
open PI.RW
namespace PI.RWS
theorem _root_.solution {k N : ℕ} (sz : Fin N → ℕ) (I : ∀ j, Fin (sz j) → Fin k)
    (hI : ∀ j, StrictMono (I j)) (a t0 : Fin k) (ht0 : t0.val = 0) :
    ∑ j, (Finset.univ.filter fun p => I j p = a).card ≤ shapeDeg sz t0 := by
  unfold shapeDeg
  rw [ht0, Finset.card_filter]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : 0 < sz j
  · rw [if_pos hj]
    refine Finset.card_le_one.2 fun p hp q hq => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact (hI j).injective (hp.trans hq.symm)
  · rw [if_neg hj]
    have hem : (Finset.univ : Finset (Fin (sz j))) = ∅ :=
      Finset.univ_eq_empty_iff.2 ⟨fun p => hj (lt_of_le_of_lt (Nat.zero_le _) p.2)⟩
    rw [hem]
    simp
end PI.RWS
