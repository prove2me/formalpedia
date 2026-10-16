-- Prove2me | solution 1 for OnDemandDelivery.Approx.last_period
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:01:40.179134+00:00
-- url     : https://prove2.me/submissions/3e640a13-ad32-4a18-82e6-432e7f309f3f

import Mathlib
import Definitions.Def_OnDemandDelivery_Approx_Setting

open scoped ENNReal NNReal
open OnDemandDelivery.Approx

namespace DeliveryResearch

theorem Hs_antitone {L : Type*} (M : Model L) (d : Demand L) {a b : ℕ}
    (hab : a ≤ b) : M.Hs b d ≤ M.Hs a d := by
  unfold Model.Hs
  exact le_iInf₂ fun Y hY => iInf₂_le_of_le Y ⟨hY.1.trans hab,hY.2⟩ le_rfl

theorem EHs_antitone {L : Type*} (M : Model L) (n : ℕ) {a b : ℕ}
    (hab : a ≤ b) : M.EHs n b ≤ M.EHs n a := by
  unfold Model.EHs
  exact ENNReal.tsum_le_tsum fun d => mul_le_mul_right (Hs_antitone M d hab) _

end DeliveryResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Sheng Liu and Zhixing Luo, arXiv:2107.13058v3, Appendix D, last period.
theorem solution {L : Type*} [Fintype L] (M : Model L) (_hM : M.Standing) (ζ : ℕ → ℕ)
    (hζ : ζ M.N ≤ M.Kbar) :
    M.EH M.N ζ = ⨅ (K : ℕ) (_ : (K : ℝ) ≤ (M.Kbar : ℝ) - (ζ M.N : ℝ)), M.EHs M.N K := by
  have hcast : ((M.Kbar - ζ M.N : ℕ) : ℝ) = (M.Kbar : ℝ) - (ζ M.N : ℝ) :=
    Nat.cast_sub hζ
  have heq : M.EH M.N ζ = M.EHs M.N (M.Kbar - ζ M.N) := by
    unfold Model.EH Model.EHs
    congr 1
    funext d
    rw [Model.H]
    simp only [lt_self_iff_false, ↓reduceDIte, Model.Hs]
  rw [heq]
  apply le_antisymm
  · refine le_iInf₂ fun K hK => DeliveryResearch.EHs_antitone M M.N ?_
    rw [← hcast] at hK
    exact_mod_cast hK
  · exact iInf₂_le_of_le (M.Kbar - ζ M.N) hcast.le le_rfl

#print axioms solution
