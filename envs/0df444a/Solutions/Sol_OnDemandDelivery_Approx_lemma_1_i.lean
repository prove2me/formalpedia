-- Prove2me | solution 1 for OnDemandDelivery.Approx.lemma_1_i
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:01:28.191794+00:00
-- url     : https://prove2.me/submissions/39bb8d76-68a1-4e8e-971c-f5bea3387833

import Mathlib
import Definitions.Def_OnDemandDelivery_Approx_Setting

open scoped ENNReal NNReal
open OnDemandDelivery.Approx

namespace DeliveryResearch

theorem H_mono {L : Type*} (M : Model L) (n : ℕ) (d : Demand L)
    (ζ₁ ζ₂ : ℕ → ℕ) (h : ζ₂ ≤ ζ₁) : M.H n d ζ₂ ≤ M.H n d ζ₁ := by
  have feasible (Y : Decision L) (hY : M.SingleFeasible (M.Kbar - ζ₁ n) d Y) :
      M.SingleFeasible (M.Kbar - ζ₂ n) d Y :=
    ⟨hY.1.trans (Nat.sub_le_sub_left (h n) _), hY.2⟩
  rw [Model.H, Model.H]
  split_ifs with hn
  · refine le_iInf₂ fun Y hY => iInf₂_le_of_le Y (feasible Y hY) ?_
    apply add_le_add le_rfl
    apply ENNReal.tsum_le_tsum
    intro d'
    apply mul_le_mul_right
    apply H_mono M (n+1) d'
    intro j
    unfold Model.next
    split_ifs
    · exact Nat.add_le_add_right (h j) _
    · exact h j
  · exact le_iInf₂ fun Y hY => iInf₂_le_of_le Y (feasible Y hY) le_rfl
termination_by M.N - n

end DeliveryResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Sheng Liu and Zhixing Luo, arXiv:2107.13058v3, Lemma 1(i).
theorem solution {L : Type*} [Fintype L] (M : Model L) (_hM : M.Standing) (n : ℕ)
    (_hn : 1 ≤ n) (_hnN : n ≤ M.N) (d : Demand L) (ζ₁ ζ₂ : ℕ → ℕ) (h : ζ₂ ≤ ζ₁) :
    M.H n d ζ₂ ≤ M.H n d ζ₁ := DeliveryResearch.H_mono M n d ζ₁ ζ₂ h

#print axioms solution
