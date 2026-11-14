-- Prove2me | solution 1 for QuantileMDP.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @shuffle
-- created : 2026-11-13T18:05:23.027322+00:00
-- url     : https://prove2.me/submissions/c014a530-0acc-4d90-98e4-e8cd1e7b369d

import Mathlib.MeasureTheory.Measure.Dirac
import Theorems.Thm_QuantileMDP_eq_6
import Theorems.Thm_QuantileMDP_theorem_1
import Definitions.Def_QuantileMDP_dpValue

open MeasureTheory Set QuantileMDP
open scoped ENNReal

namespace QuantileMDP

private theorem quantile_dirac_zero (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    quantile (Measure.dirac (0 : ℝ)) τ = 0 := by
  have hl (x : ℝ) : Measure.dirac (0 : ℝ) (Ici x) = 1 ↔ x ≤ 0 := by
    rw [Measure.dirac_apply]
    by_cases hx : x ≤ 0 <;> simp [Set.indicator, hx]
  have hr (x : ℝ) : Measure.dirac (0 : ℝ) (Iic x) = 1 ↔ 0 ≤ x := by
    rw [Measure.dirac_apply]
    by_cases hx : 0 ≤ x <;> simp [Set.indicator, hx]
  rw [quantile]
  split_ifs with hz h1
  · apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact EReal.coe_nonpos.mpr ((hl x).mp hx)
    · exact le_sSup ⟨0, (hl 0).mpr le_rfl, EReal.coe_zero⟩
  · apply le_antisymm
    · exact sInf_le ⟨0, (hr 0).mpr le_rfl, EReal.coe_zero⟩
    · refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      exact EReal.coe_nonneg.mpr ((hr x).mp hx)
  · have htpos : 0 < ENNReal.ofReal τ := ENNReal.ofReal_pos.mpr (lt_of_le_of_ne hτ.1 (Ne.symm hz))
    have htle : ENNReal.ofReal τ ≤ 1 := ENNReal.ofReal_le_one.mpr hτ.2
    apply le_antisymm
    · refine sInf_le ⟨0, ?_, EReal.coe_zero⟩
      change ENNReal.ofReal τ ≤ Measure.dirac (0 : ℝ) (Iic 0)
      rw [(hr 0).mpr le_rfl]
      exact htle
    · refine le_sInf ?_
      rintro _ ⟨x, hx, rfl⟩
      apply EReal.coe_nonneg.mpr
      by_contra! h
      have hzero : Measure.dirac (0 : ℝ) (Iic x) = 0 := by
        simp [Set.indicator, not_le_of_gt h]
      exact (not_le_of_gt htpos) (hzero ▸ hx)

private theorem optValue_zero {S A : Type*} [Fintype S] (M : Model S A)
    (T t : ℕ) (ht : T - t = 0) (s : S) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    optValue M T t s τ = 0 := by
  have hlaw (π : Policy S A) : rewardLaw (M.shift t) (T - t) π s = Measure.dirac 0 := by
    rw [ht]
    simp [rewardLaw, pathWeight, pathReward]
  have hval (π : Policy S A) : quantile (rewardLaw (M.shift t) (T - t) π s) τ = 0 := by
    rw [hlaw, quantile_dirac_zero τ hτ]
  let π : Policy S A := fun k h => ((M.shift t).adm_nonempty k (h (Fin.last k))).choose
  have hπ : (M.shift t).Admissible π := fun k h =>
    ((M.shift t).adm_nonempty k (h (Fin.last k))).choose_spec
  exact le_antisymm (iSup_le fun ρ => iSup_le fun _ => (hval ρ).le)
    ((hval π).ge.trans (le_iSup_of_le π (le_iSup_of_le hπ le_rfl)))

private theorem dpAux_eq_value {S A : Type*} [Fintype S] [Fintype A] (M : Model S A)
    (T n t : ℕ) (hn : T - t = n) (s : S) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1) :
    dpAux M n t s τ = optValue M T t s τ := by
  induction n generalizing t s τ with
  | zero => exact (optValue_zero M T t hn s τ hτ).symm
  | succ n ih =>
    have ht : t < T := by omega
    have hn' : T - (t + 1) = n := by omega
    rw [(eq_6 M T t s τ).1, dpAux]
    congr 1
    funext a
    congr 1
    funext ha
    rw [(theorem_1 M T t ht s a ha τ hτ).1]
    unfold opt
    congr 1
    funext q
    congr 1
    funext hq
    simp_rw [fun i => ih (t + 1) hn' i (q i) (hq.1 i)]

private theorem shift_zero {S A : Type*} (M : Model S A) : M.shift 0 = M := by
  cases M
  simp [Model.shift]

end QuantileMDP

/-- Backward dynamic programming computes the attained optimal quantile. -/
theorem solution {S A : Type*} [Fintype S] [Fintype A] (M : Model S A) (T : ℕ) (s : S) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest {x : EReal | ∃ π : Policy S A, M.Admissible π ∧
        x = quantile (rewardLaw M T π s) τ} (dpValue M T 0 s τ) := by
  have hdp : dpValue M T 0 s τ = optValue M T 0 s τ :=
    dpAux_eq_value M T (T - 0) 0 rfl s τ hτ
  rw [hdp]
  constructor
  · cases T with
    | zero =>
      let π : Policy S A := fun k h => (M.adm_nonempty k (h (Fin.last k))).choose
      have hπ : M.Admissible π := fun k h => (M.adm_nonempty k (h (Fin.last k))).choose_spec
      have hlaw : rewardLaw M 0 π s = Measure.dirac 0 := by
        simp [rewardLaw, pathWeight, pathReward]
      exact ⟨π, hπ, by rw [optValue_zero M 0 0 rfl s τ hτ, hlaw, quantile_dirac_zero τ hτ]⟩
    | succ T =>
      obtain ⟨a, ha, hva⟩ := (eq_6 M (T + 1) 0 s τ).2
      obtain ⟨π, hπ, _, hval⟩ := (theorem_1 M (T + 1) 0 (Nat.zero_lt_succ T) s a ha τ hτ).2.2
      rw [shift_zero] at hπ hval
      exact ⟨π, hπ, (hval.trans hva).symm⟩
  · rintro x ⟨π, hπ, rfl⟩
    have hπ' : (M.shift 0).Admissible π := by simpa only [shift_zero] using hπ
    have h : quantile (rewardLaw (M.shift 0) (T - 0) π s) τ ≤ optValue M T 0 s τ :=
      le_iSup_of_le π (le_iSup_of_le hπ' le_rfl)
    simpa only [shift_zero, Nat.sub_zero] using h
