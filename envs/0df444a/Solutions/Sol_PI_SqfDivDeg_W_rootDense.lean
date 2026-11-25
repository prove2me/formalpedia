-- Prove2me | solution 1 for PI.SqfDivDeg.W.rootDense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:41.059325+00:00
-- url     : https://prove2.me/submissions/73510d2e-bda4-4a0b-90d5-6555120c099a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_MonicFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe
import Theorems.Thm_PI_SqfDivDeg_W_rt_one
import Theorems.Thm_PI_SqfDivDeg_W_card_fib_ge
import Theorems.Thm_PI_SqfDivDeg_W_card_monic_two_roots_le
import Theorems.Thm_PI_SqfDivDeg_W_pt
import Theorems.Thm_PI_SqfDivDeg_W_sum_rts
import Theorems.Thm_PI_SqfDivDeg_W_sum_offDiag
import Theorems.Thm_PI_SqfDivDeg_W_card_Rt_eq
import Theorems.Thm_PI_SqfDivDeg_W_card_Mon


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open PI PI.SqfDivDeg PI.SqfDivDeg.W
open Classical
namespace PI.SqfDivDeg.W
theorem _root_.solution : RootDense := by
  intro g _ n hn
  obtain rfl | hn2 : n = 1 ∨ 2 ≤ n := by omega
  · rw [rt_one, card_Mon]
    omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hpt : ∑ f ∈ Mon g (m + 2), 2 * (rts f).card ≤
      ∑ f ∈ Mon g (m + 2), ((rts f).offDiag.card + 2 * (if (rts f).card = 0 then 0 else 1)) := by
    refine Finset.sum_le_sum (fun f _ => ?_)
    rw [Finset.offDiag_card]
    exact pt _
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← card_Rt_eq] at hpt
  have h1 : g * g ^ (m + 1) ≤ ∑ f ∈ Mon g (m + 2), (rts f).card := by
    rw [sum_rts]
    have := Finset.card_nsmul_le_sum (univ : Finset (ZMod g))
      (fun c => ((Mon g (m + 1 + 1)).filter (fun f => f.IsRoot c)).card) (g ^ (m + 1))
      (fun c _ => card_fib_ge (m + 1) c)
    simpa [ZMod.card] using this
  have h2 : ∑ f ∈ Mon g (m + 2), (rts f).offDiag.card ≤ (g * g - g) * g ^ m := by
    rw [sum_offDiag]
    have := Finset.sum_le_card_nsmul ((univ : Finset (ZMod g)).offDiag)
      (fun x => ((Mon g (m + 2)).filter (fun f => f.IsRoot x.1 ∧ f.IsRoot x.2)).card) (g ^ m)
      (fun x hx => card_monic_two_roots_le m x.1 x.2 (Finset.mem_offDiag.mp hx).2.2)
    simpa [Finset.offDiag_card, ZMod.card] using this
  have hB : (g * g - g) * g ^ m ≤ g * g * g ^ m := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have eA : g ^ (m + 2) = g * g * g ^ m := by ring
  have eA' : g * g ^ (m + 1) = g * g * g ^ m := by ring
  rw [eA]
  rw [eA'] at h1
  omega
end PI.SqfDivDeg.W
