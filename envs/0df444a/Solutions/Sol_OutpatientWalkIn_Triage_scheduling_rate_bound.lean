-- Prove2me | solution 1 for OutpatientWalkIn.Triage.scheduling_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:48:01.533801+00:00
-- url     : https://prove2.me/submissions/a597bb03-56c6-4bb7-845f-078fd9d6cbee

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue
import Definitions.Def_OutpatientWalkIn_Triage_Setting
import Theorems.Thm_OutpatientWalkIn_SmallCap_proposition_C_2_delta

namespace P6SRB

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

theorem eq_delta_char (M : Model) (hM : M.Standing) (μS : ℝ) (e : ObsStrategy)
    (he : M.IsObsEq μS e) :
    M.R - M.CD * e.δ = e.pW / (e.pW + e.pB) * M.u2W μS e.pW + e.pB / (e.pW + e.pB) * 0 := by
  obtain ⟨_, _, _, hCD, _⟩ := hM
  obtain ⟨hδ, _, _, _, h5, h6, _⟩ := he
  set U := e.pW / (e.pW + e.pB) * M.u2W μS e.pW + e.pB / (e.pW + e.pB) * 0
  have hge : M.R - M.CD * e.δ ≥ U := h5 e.δ hδ le_rfl
  by_contra hne
  have hgt : M.R - M.CD * e.δ > U := lt_of_le_of_ne hge (Ne.symm hne)
  have := h6 (e.δ + (M.R - M.CD * e.δ - U) / (2 * M.CD)) (by
    have : 0 < (M.R - M.CD * e.δ - U) / (2 * M.CD) := div_pos (by linarith) (by linarith)
    linarith)
  unfold Model.u2S at this
  have hc : M.CD * (e.δ + (M.R - M.CD * e.δ - U) / (2 * M.CD)) =
      M.CD * e.δ + (M.R - M.CD * e.δ - U) / 2 := by field_simp
  rw [hc] at this
  linarith

/-- The equilibrium threshold never exceeds `R / C_D`. -/
theorem delta_le (M : Model) (hM : M.Standing) (μS : ℝ) (e : ObsStrategy)
    (he : M.IsObsEq μS e) : e.δ ≤ M.R / M.CD := by
  have hc := eq_delta_char M hM μS e he
  have hCD : 0 < M.CD := hM.2.2.2.1
  obtain ⟨_, hpW, hpB, hsum, _, _, _, h8, _⟩ := he
  have hU : 0 ≤ e.pW / (e.pW + e.pB) * M.u2W μS e.pW := by
    rcases h8 with h | h
    · rw [h]; simp
    · exact mul_nonneg (div_nonneg hpW hsum.le) h
  rw [le_div_iff₀ hCD]
  nlinarith

end P6SRB

open OutpatientWalkIn.Triage

theorem solution (M : Model) (hM : M.Standing) :
    ∀ μS ∈ Set.Ico 0 M.mu, ∀ e : ObsStrategy, M.IsObsEq μS e →
      M.lam * (1 - blockProb M.lam e.δ μS) ≤ M.lam * (1 - blockProb M.lam (M.R / M.CD) μS) := by
  intro μS hμS e he
  have hlam : 0 < M.lam := hM.1
  have hδ0 : 0 ≤ e.δ := he.1
  have hR : 0 ≤ M.R / M.CD := div_nonneg hM.2.2.1.le hM.2.2.2.1.le
  have hle := P6SRB.delta_le M hM μS e he
  suffices h : blockProb M.lam (M.R / M.CD) μS ≤ blockProb M.lam e.δ μS by
    nlinarith
  rcases eq_or_lt_of_le hμS.1 with h0 | hpos
  · subst h0; unfold blockProb; simp
  · rw [P6SRB.blockProb_eq _ _ _ hμS.1 hδ0, P6SRB.blockProb_eq _ _ _ hμS.1 hR]
    exact ((OutpatientWalkIn.SmallCap.proposition_C_2_delta M.lam hlam μS hpos).1.antitoneOn)
      (Set.mem_Ici.2 hδ0) (Set.mem_Ici.2 hR) hle
