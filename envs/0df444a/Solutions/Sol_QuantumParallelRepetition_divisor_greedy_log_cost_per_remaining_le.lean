-- Prove2me | solution 1 for QuantumParallelRepetition.divisor_greedy_log_cost_per_remaining_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/0aa68d0e-6e3e-4bb6-9719-eff43d8dbd40

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_postselection_log_cost_le
import Theorems.Thm_QuantumParallelRepetition_sourceAnswerAlphabetBound_log_nonneg
import Theorems.Thm_QuantumParallelRepetition_fullHistoryAnswerCount_le_sourceAnswerAlphabetBound_pow
import Theorems.Thm_QuantumParallelRepetition_fullHistoryAnswerCount_pos_of_postselection
import Theorems.Thm_QuantumParallelRepetition_divisor_greedy_remaining_bounds

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n))
    {η : ℝ} (hη : 0 < η)
    {q : ℕ} (hq : 2 ≤ q)
    (D : Finset (Fin n))
    (hD : D.card < n / q)
    (hwitness :
      Real.exp (-(η / (4 * (q : ℝ))) * (n : ℝ)) <
        S.winProbability)
    (hmass :
      S.winProbability ≤
        (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) :
    Real.log
        (fullHistoryAnswerCount (A := A) (B := B) D /
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)) /
        ((Finset.univ \ D).card : ℝ) ≤
      (2 * Real.log (sourceAnswerAlphabetBound A B) + η / 2) /
        (q : ℝ) := by
  classical
  let p : ℝ :=
    (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
  let m : ℕ := (Finset.univ \ D).card
  let k : ℝ := sourceAnswerAlphabetBound A B
  have hqpos : 0 < q := by omega
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hθ : 0 < S.winProbability :=
    lt_trans (Real.exp_pos _) hwitness
  have hp : 0 < p := lt_of_lt_of_le hθ hmass
  have hN : 0 < fullHistoryAnswerCount (A := A) (B := B) D :=
    fullHistoryAnswerCount_pos_of_postselection G n S D ∅
      (Finset.empty_subset _) hp
  have hklog : 0 ≤ Real.log k :=
    sourceAnswerAlphabetBound_log_nonneg A B
  have hcount :
      Real.log (fullHistoryAnswerCount (A := A) (B := B) D) ≤
        (D.card : ℝ) * Real.log k := by
    calc
      Real.log (fullHistoryAnswerCount (A := A) (B := B) D) ≤
          Real.log (k ^ D.card) :=
        Real.log_le_log hN
          (fullHistoryAnswerCount_le_sourceAnswerAlphabetBound_pow D)
      _ = (D.card : ℝ) * Real.log k := Real.log_pow _ _
  have hlogθ :
      Real.log (1 / S.winProbability) <
        (η / (4 * (q : ℝ))) * (n : ℝ) := by
    have hlog := (Real.lt_log_iff_exp_lt hθ).mpr hwitness
    rw [one_div, Real.log_inv]
    linarith
  have hlogp :
      Real.log (1 / p) ≤
        (η / (4 * (q : ℝ))) * (n : ℝ) := by
    exact (postselection_log_cost_le hθ hmass).trans hlogθ.le
  have htotal :
      Real.log
          (fullHistoryAnswerCount (A := A) (B := B) D / p) ≤
        (D.card : ℝ) * Real.log k +
          (η / (4 * (q : ℝ))) * (n : ℝ) := by
    rw [Real.log_div hN.ne' hp.ne']
    rw [one_div, Real.log_inv] at hlogp
    linarith
  obtain ⟨hmnat, hnmnat, hdqmnat⟩ :=
    divisor_greedy_remaining_bounds hq hD
  have hm : 0 < (m : ℝ) := by
    exact_mod_cast hmnat
  have hnm : (n : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast hnmnat
  have hdqm :
      (D.card : ℝ) * (q : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast hdqmnat
  have hdratio :
      (D.card : ℝ) / (m : ℝ) ≤ 2 / (q : ℝ) := by
    exact (div_le_div_iff₀ hm hqreal).mpr hdqm
  have hnratio : (n : ℝ) / (m : ℝ) ≤ 2 := by
    exact (div_le_iff₀ hm).mpr hnm
  have hrate : 0 ≤ η / (4 * (q : ℝ)) := by positivity
  change
    Real.log (fullHistoryAnswerCount (A := A) (B := B) D / p) /
        (m : ℝ) ≤
      (2 * Real.log k + η / 2) / (q : ℝ)
  calc
    Real.log (fullHistoryAnswerCount (A := A) (B := B) D / p) /
        (m : ℝ) ≤
      ((D.card : ℝ) * Real.log k +
        (η / (4 * (q : ℝ))) * (n : ℝ)) / (m : ℝ) := by
        exact (div_le_div_iff_of_pos_right hm).mpr htotal
    _ = ((D.card : ℝ) / (m : ℝ)) * Real.log k +
        (η / (4 * (q : ℝ))) * ((n : ℝ) / (m : ℝ)) := by
          ring
    _ ≤ (2 / (q : ℝ)) * Real.log k +
        (η / (4 * (q : ℝ))) * 2 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hdratio hklog)
            (mul_le_mul_of_nonneg_left hnratio hrate)
    _ = (2 * Real.log k + η / 2) / (q : ℝ) := by
      field_simp
      ring
end QuantumParallelRepetition
