-- Prove2me | solution 1 for PrivPCP.corollary_8_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:21:14.60618+00:00
-- url     : https://prove2.me/submissions/a83e427e-5572-4bdc-bd07-4f0d148158f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PrivPCP_HasPrivatePCP
import Definitions.Def_PrivPCP_PunctRSPE
import Theorems.Thm_PrivPCP_corollary_8_3_cond
import Theorems.Thm_PrivPCP_theorem_4_11

theorem solution : ∃ C : ℝ, 0 < C ∧
    (∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      (∀ r : ℕ, 2 ≤ r → r ≤ k → PrivPCP.PunctRSPE r (1 / 128) 4 ρ) → PrivPCP.HasPrivatePCP C k ρ) ∧
    (∃ ρ₂ : ℝ, 0 < ρ₂ ∧ ρ₂ ≤ 1 ∧ PrivPCP.HasPrivatePCP C 2 ρ₂) := by
  obtain ⟨C, hC, ha⟩ := PrivPCP.corollary_8_3_cond
  refine ⟨C, hC, ha, ?_⟩
  obtain ⟨c, hc, h411⟩ := PrivPCP.theorem_4_11
  obtain ⟨ρ, hρlow, hρ1, hpe⟩ := h411 (1 / 128) (by norm_num) (by norm_num) 4 (by norm_num)
  have hpos : 0 < ρ := lt_of_lt_of_le (by positivity) hρlow
  refine ⟨ρ, hpos, hρ1, ha 2 le_rfl ρ hpos hρ1 (fun r hr hr' => ?_)⟩
  obtain rfl : r = 2 := by omega
  exact hpe
