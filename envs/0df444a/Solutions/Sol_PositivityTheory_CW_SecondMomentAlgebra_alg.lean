-- Prove2me | solution 1 for PositivityTheory.CW.SecondMomentAlgebra.alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:44.608851+00:00
-- url     : https://prove2.me/submissions/cc96a190-fd67-4878-8143-fba82c7d6212

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MatrixActionSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.SecondMomentAlgebra
namespace PositivityTheory.CW.SecondMomentAlgebra
theorem _root_.solution (n m : ℕ) (C1 C2 s T : ℝ) (hn : (1:ℝ) ≤ n) (hm : 1 ≤ m) (hC2 : 0 < C2) (hs : 1 ≤ s)
    (hs2 : 2 * C1 * (2 * (n:ℝ)) ^ m ≤ s)
    (h : (s ^ 2 / (2 * n)) ^ m ≤ C1 * s ^ (2 * m - 1) + C2 * s ^ (2 * m - 2) * T) :
    1 / (2 * (2 * (n:ℝ)) ^ m * C2) * s ^ 2 ≤ T := by
  have hA : 0 < (2 * (n:ℝ)) ^ m := by positivity
  have hs0 : 0 < s := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) - 2 = 2 * k := by omega
  rw [e1, e2, div_pow, ← pow_mul] at h
  set A := (2 * (n:ℝ)) ^ (k + 1) with hAdef
  have hP : 0 < s ^ (2 * k) := by positivity
  have f1 : s ^ (2 * (k + 1)) = s ^ (2 * k) * s ^ 2 := by ring
  have f2 : s ^ (2 * k + 1) = s ^ (2 * k) * s := by ring
  rw [f1, f2, div_le_iff₀ hA] at h
  have h' : s ^ (2 * k) * s ^ 2 ≤ s ^ (2 * k) * (A * C1 * s + A * C2 * T) := by
    calc s ^ (2 * k) * s ^ 2 ≤ (C1 * (s ^ (2 * k) * s) + C2 * s ^ (2 * k) * T) * A := h
      _ = s ^ (2 * k) * (A * C1 * s + A * C2 * T) := by ring
  have h'' : s ^ 2 ≤ A * C1 * s + A * C2 * T := le_of_mul_le_mul_left h' hP
  have h2 : 2 * (A * C1 * s) ≤ s ^ 2 := by
    have := mul_le_mul_of_nonneg_right hs2 hs0.le
    nlinarith
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith
end PositivityTheory.CW.SecondMomentAlgebra
