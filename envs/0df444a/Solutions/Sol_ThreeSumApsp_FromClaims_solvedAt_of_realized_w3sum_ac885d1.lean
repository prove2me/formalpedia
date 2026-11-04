-- Prove2me | solution 1 for ThreeSumApsp.FromClaims.solvedAt_of_realized_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:49:46.616145+00:00
-- url     : https://prove2.me/submissions/269ff5a0-5880-430d-b5df-3ba2b1189ec8

import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_TimeClaims_Sec3_Definitions
import Definitions.Def_Submission_ThreeSumApsp_RunningTimes_FromClaims_Bounds
import Theorems.Thm_ThreeSumApsp_FromClaims_cast_pow_eq
import Theorems.Thm_ThreeSumApsp_Dominated_of_eventually_add_one
import Theorems.Thm_ThreeSumApsp_IsBigOPow_mono
import Theorems.Thm_ThreeSumApsp_IsPowLittleO_mono
import Theorems.Thm_ThreeSumApsp_IsPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_UpperPowPolylog_mono
import Theorems.Thm_ThreeSumApsp_WordRam_IsDataStructure_mono
import Theorems.Thm_ThreeSumApsp_WordRam_Solves_mono
import Theorems.Thm_ThreeSumApsp_WordRam_solvedInTimeAt_iff


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.FromClaims
open ThreeSumApsp.WordRam
open EndStatement (Instr)
namespace ThreeSumApsp.FromClaims
theorem _root_.solution {Q : EndStatement.Problem} (T : ℕ → ℝ → ℝ) (κ : ℕ)
    (hR : Realized Q T) {C a : ℝ} {e : ℕ}
    (hev : ∀ᶠ n : ℕ in Filter.atTop,
      T n ((n : ℝ) ^ ((κ : ℕ) : ℝ)) ≤ C * ((n : ℝ) ^ a * Real.log n ^ e)) :
    SolvedInTimeAt Q κ a e := by
  obtain ⟨P, b, c, hc, hS⟩ := hR κ
  have hg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ a * Real.log n ^ e := fun n =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Real.log_natCast_nonneg _) _)
  -- a bound for all large `n` gives a bound for all `n`
  obtain ⟨C', hC', hb⟩ := Dominated.of_eventually_add_one hev hg
  refine solvedInTimeAt_iff.2 ⟨P, b, c * C' + c, hS.mono le_rfl (fun x hx => hx) fun x hx => ?_⟩
  have hU : ((x.U : ℕ) : ℝ) = (x.n : ℝ) ^ ((κ : ℕ) : ℝ) := by
    rw [hx]
    exact cast_pow_eq _ _
  change c * max (T x.n ((x.U : ℕ) : ℝ)) 0 + c ≤ _
  rw [hU]
  -- `c max(T, 0) + c ≤ c C' (X + 1) + c ≤ (c C' + c) (X + 1)`, where `X = n^a (log n)^e ≥ 0`
  have hcT : c * max (T x.n ((x.n : ℝ) ^ ((κ : ℕ) : ℝ))) 0 ≤
      c * (C' * ((x.n : ℝ) ^ a * Real.log x.n ^ e + 1)) :=
    mul_le_mul_of_nonneg_left (max_le (hb x.n trivial) (mul_nonneg hC' (by linarith [hg x.n]))) hc
  linarith [mul_nonneg hc (hg x.n)]
end ThreeSumApsp.FromClaims
