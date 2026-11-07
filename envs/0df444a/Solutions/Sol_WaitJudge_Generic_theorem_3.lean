-- Prove2me | solution 1 for WaitJudge.Generic.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T23:19:42.419852+00:00
-- url     : https://prove2.me/submissions/d4468dcd-04bd-4709-8eae-eb8561ef435c

import Mathlib
import Definitions.Def_WaitJudge_Generic_Setting
import Theorems.Thm_WaitJudge_Generic_prob_violation_eq_sum_integral
import Theorems.Thm_WaitJudge_Generic_moment_conditions
import Theorems.Thm_WaitJudge_Generic_weak_duality_N
import Theorems.Thm_WaitJudge_Generic_gammaStarN_eq_gammaStar31

open MeasureTheory WaitJudge.Generic

theorem solution
    {S Δ : Type*} [Nonempty S] [MeasurableSpace S] [MeasurableSpace Δ]
    (P : Measure Δ) [IsProbabilityMeasure P]
    (f : S → ℝ) (X : Set S) (Xδ : Δ → Set S)
    {p : ℕ} (tb : Fin p → S → ℝ)
    (hA1 : Assumption1 f X Xδ tb)
    (hA2 : Assumption2 f X Xδ tb P)
    (hmeas : MeasurabilityPins f X Xδ tb)
    (N : ℕ) (hN : 0 < N) (ε : ℕ → ℝ)
    (hε : ∀ k ≤ N, 0 ≤ ε k ∧ ε k ≤ 1) :
    (Measure.pi fun _ : Fin N => P)
      {ω : Fin N → Δ | ε (sstar f X Xδ tb ω) <
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω)} ≤
      ENNReal.ofReal (gammaStar31 N ε) := by
  set E := {ω : Fin N → Δ | ε (sstar f X Xδ tb ω) <
        ScenarioApproach.Nonconvex.violation P Xδ (xstar f X Xδ tb ω)}
  have hsum := prob_violation_eq_sum_integral P f X Xδ tb hA1 hA2 hmeas N hN ε hε
  have hmom := moment_conditions P f X Xδ tb hA1 hA2 hmeas
  have hfin : ∀ k ≤ N, Fk f X Xδ tb P k Set.univ < ⊤ := by
    intro k _
    unfold Fk
    exact measure_lt_top _ _
  -- the dual feasible set is nonempty
  have hne : {y : ℝ | ∃ lam : ℕ → ℝ,
      IsFeasibleDualN N ε lam ∧ y = ∑ m ∈ Finset.range (N + 1), lam m}.Nonempty := by
    refine ⟨_, fun m => if m = N then 1 else 0, ?_, rfl⟩
    intro k hk t ht
    have hsplit : ∑ m ∈ Finset.Icc k N, (if m = N then (1:ℝ) else 0) * (m.choose k : ℝ) * t ^ (m - k)
        = (N.choose k : ℝ) * t ^ (N - k) := by
      rw [Finset.sum_eq_single N]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩) h
    rw [hsplit]
    have h0 : 0 ≤ (N.choose k : ℝ) * t ^ (N - k) := by
      have := ht.1; positivity
    have hi : Set.indicator (Set.Ico 0 (1 - ε k)) (fun _ => (1 : ℝ)) t ≤ 1 := by
      unfold Set.indicator; split_ifs <;> norm_num
    calc (N.choose k : ℝ) * t ^ (N - k) * Set.indicator (Set.Ico 0 (1 - ε k)) (fun _ => (1 : ℝ)) t
        ≤ (N.choose k : ℝ) * t ^ (N - k) * 1 := mul_le_mul_of_nonneg_left hi h0
      _ = _ := mul_one _
  have hle : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) *
      ∫ v in Set.Ioc (ε k) 1, (1 - v) ^ (N - k) ∂(Fk f X Xδ tb P k) ≤ gammaStarDualN N ε := by
    apply le_csInf hne
    rintro y ⟨lam, hlam, rfl⟩
    exact weak_duality_N N ε hε (fun k => Fk f X Xδ tb P k) hfin (fun m _ => hmom m) lam hlam
  rw [gammaStarN_eq_gammaStar31] at hle
  rw [← hsum] at hle
  calc (Measure.pi fun _ : Fin N => P) E
      = ENNReal.ofReal (((Measure.pi fun _ : Fin N => P) E).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (gammaStar31 N ε) := ENNReal.ofReal_le_ofReal hle

