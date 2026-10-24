-- Prove2me | solution 1 for OutpatientWalkIn.Triage.proposition_1_obs
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:48:02.424758+00:00
-- url     : https://prove2.me/submissions/51439c90-ca1e-4225-81e0-d7dfdc4ed8ee

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting
import Theorems.Thm_OutpatientWalkIn_SmallCap_proposition_1_obs_exists

namespace P6Ex

open OutpatientWalkIn.Triage

theorem blockProb_eq (lam δ μS : ℝ) (hμ : 0 ≤ μS) (hδ : 0 ≤ δ) :
    blockProb lam δ μS = OutpatientWalkIn.SmallCap.blockProb lam δ μS := by
  unfold blockProb OutpatientWalkIn.SmallCap.blockProb OutpatientWalkIn.SmallCap.bufferK
    OutpatientWalkIn.SmallCap.bufferP
  rcases eq_or_lt_of_le hμ with h | h
  · subst h; simp
  · have h1 : ¬ (μS ≤ 0 ∨ δ < 0) := by push_neg; exact ⟨h, hδ⟩
    rw [if_neg h1, if_neg h.ne']
    rfl

end P6Ex

open OutpatientWalkIn.Triage

theorem solution (M : Model) (hM : M.Standing) :
    ∀ μS ∈ Set.Ico 0 M.mu, ∃ e : ObsStrategy, M.IsObsEq μS e := by
  intro μS hμS
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hM
  let N : OutpatientWalkIn.SmallCap.Model :=
    ⟨M.lam, M.lamE, M.R, M.CD, M.CW, M.CL, M.CO, M.mu, M.w, M.o⟩
  have hN : N.Standing := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  obtain ⟨f, hf⟩ := OutpatientWalkIn.SmallCap.proposition_1_obs_exists N hN μS hμS
  refine ⟨⟨f.delta, f.pW, f.pB⟩, hf.delta_nonneg, hf.pW_nonneg, hf.pB_nonneg, hf.sum_pos,
    hf.cond6, hf.cond7, ?_, hf.cond9, hf.cond10⟩
  show f.pW + f.pB = blockProb M.lam f.delta μS
  rw [P6Ex.blockProb_eq _ _ _ hμS.1 hf.delta_nonneg]
  exact hf.cond8
