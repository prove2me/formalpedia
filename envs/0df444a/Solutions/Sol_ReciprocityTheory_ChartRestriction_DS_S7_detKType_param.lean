-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.detKType_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:26:29.586395+00:00
-- url     : https://prove2.me/submissions/efc42f90-3ed2-426b-9de7-c521d08807f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_InhabA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SmulOneMemUnitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_card_filter_fin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lam_hol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (p q : ℕ) (a b : ℤ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    lowK (epsHol p q) (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q)) = detWt p q a b ∧
      ((p : ℝ) + q - 1 < (a : ℝ) - b →
        IsHCParam (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q)) ∧
        GapAtLeast (epsHol p q) (detWt p q a b - rhoN (epsHol p q) + rhoC (epsHol p q))
          ((a : ℝ) - b - (p + q) + 1) ∧
        1 ≤ q0 (epsHol p q)) := by
  refine ⟨?_, fun hab => ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · funext i
    simp only [lowK, Pi.add_apply, Pi.sub_apply]
    ring
  ·
    intro i j hij
    have hij' : (i : ℕ) < j := hij
    rw [lam_hol, lam_hol]
    have hij'' : ((i : ℕ) : ℝ) < (j : ℕ) := by exact_mod_cast hij'
    by_cases hi : (i : ℕ) < p <;> by_cases hj : (j : ℕ) < p
    · rw [if_pos hi, if_pos hj]
      linarith
    · rw [if_pos hi, if_neg hj]
      have h1 : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hi
      have h2 : (p : ℝ) ≤ (j : ℕ) := by exact_mod_cast (not_lt.1 hj)
      linarith
    · exfalso
      omega
    · rw [if_neg hi, if_neg hj]
      linarith
  · intro i
    rw [lam_hol]
    split_ifs with h
    · exact ⟨a - q - (i : ℕ), by push_cast; ring⟩
    · exact ⟨b - (i : ℕ) + p, by push_cast; ring⟩
  · intro x y hxy
    rw [lam_hol, lam_hol]
    by_cases hx : (x : ℕ) < p <;> by_cases hy : (y : ℕ) < p
    · exact absurd (by simp [epsHol, hx, hy]) hxy
    · rw [if_pos hx, if_neg hy]
      have h1 : ((x : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hx
      have h2 : (p : ℝ) ≤ (y : ℕ) := by exact_mod_cast (not_lt.1 hy)
      exact le_trans (by linarith) (le_abs_self _)
    · rw [if_neg hx, if_pos hy, abs_sub_comm]
      have h1 : ((y : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hy
      have h2 : (p : ℝ) ≤ (x : ℕ) := by exact_mod_cast (not_lt.1 hx)
      exact le_trans (by linarith) (le_abs_self _)
    · exact absurd (by simp [epsHol, hx, hy]) hxy
  · have hP : pOf (epsHol p q) = p := by
      unfold pOf
      rw [card_filter_fin _ 0 p (by omega) fun b => by
        have := b.2
        simp only [epsHol, decide_eq_true_eq]
        omega]
      omega
    have hQ : qOf (epsHol p q) = q := by
      unfold qOf
      rw [card_filter_fin _ p (p + q) le_rfl fun b => by
        have := b.2
        simp only [epsHol, decide_eq_false_iff_not]
        omega]
      omega
    simp only [q0, hP, hQ]
    omega
end ReciprocityTheory.ChartRestriction.DS.S7
