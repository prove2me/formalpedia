-- Prove2me | solution 1 for ZhangJasinPricing.Cyclic.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:01:33.334777+00:00
-- url     : https://prove2.me/submissions/4160e674-3bf9-40ca-8d17-853b483f0ada

import Mathlib
import Definitions.Def_ZhangJasinPricing_Cyclic_Analysis

open MeasureTheory
open ZhangJasinPricing.Cyclic

noncomputable def zjZero : Model Unit where
  M := 2
  K := 1
  M_ge := le_rfl
  K_ge := le_rfl
  price := fun i => if i = 0 then 1 else 0
  price_nonneg := by intro i _; split_ifs <;> norm_num
  price_order := by
    intro i j hij hj
    have hi : i = 0 := by omega
    have hj1 : j = 1 := by omega
    subst hi hj1; norm_num
  law := Measure.dirac ()
  probability := inferInstance
  cohort := fun _ _ _ _ => 0
  mean := fun _ _ => 0
  nonneg := by intros; exact le_rfl
  measurable := by intros; exact measurable_const
  integrable := by intros; exact integrable_zero _ _ _
  mean_eq := by intros; simp
  variance_finite := by intros; simp

lemma zj_avg (w : Word) : averageRevenue zjZero w = 0 := by
  simp [averageRevenue, cycleRevenue, demand, zjZero]

lemma zj_bench (m : Mode) : benchmark zjZero m = 0 := by
  unfold benchmark
  have : averageRevenue zjZero '' PolicyClass zjZero m ⊆ {0} := by
    rintro _ ⟨w, -, rfl⟩; simp [zj_avg]
  rcases (averageRevenue zjZero '' PolicyClass zjZero m).eq_empty_or_nonempty with h | h
  · rw [h, Real.sSup_empty]
  · rw [(Set.subset_singleton_iff_eq.mp this).resolve_left h.ne_empty, csSup_singleton]

lemma zj_exp (a : Parameter) (s : ℕ) : experiment zjZero a s = fun _ => 0 := by
  funext ω; simp [experiment, zjZero]

lemma zj_sg_zero :
    HighDimProb.Concentration.subgaussianNorm zjZero.law (fun _ => (0:ℝ)) ≤ 1 := by
  unfold HighDimProb.Concentration.subgaussianNorm
  refine iInf_le_of_le 1 (iInf_le_of_le one_pos (iInf_le_of_le ?_ (iInf_le_of_le ?_ ?_)))
  · show Integrable _ (Measure.dirac ())
    exact integrable_const _
  · simp [zjZero]
  · simp

lemma zj_A1 : Assumption1 zjZero := by
  intro a _ s
  have hm : parameterMean zjZero a = 0 := by simp [parameterMean, zj_exp]
  refine ⟨by rw [zj_exp]; exact zj_sg_zero, ?_⟩
  have : (fun ω => experiment zjZero a s ω - parameterMean zjZero a) = fun _ => (0:ℝ) := by
    funext ω; simp [zj_exp, hm]
  rw [this]
  exact lt_of_le_of_lt zj_sg_zero ENNReal.one_lt_top

noncomputable def zjInit : Initialization 2 1 where
  tests := (parameters 2 1).toList
  valid := fun a h => (Finset.mem_toList).1 h
  covers := fun a h => (Finset.mem_toList).2 h

/-- running argmax over indices 0..k -/
noncomputable def zjBest (v : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | k+1 => if v (zjBest v k) < v (k+1) then k+1 else zjBest v k

lemma zjBest_le (v : ℕ → ℝ) (k : ℕ) : zjBest v k ≤ k := by
  induction k with
  | zero => simp [zjBest]
  | succ k ih => simp only [zjBest]; split_ifs <;> omega

lemma zjBest_max (v : ℕ → ℝ) (k : ℕ) : ∀ j ≤ k, v j ≤ v (zjBest v k) := by
  induction k with
  | zero => intro j hj; simp [zjBest, show j = 0 by omega]
  | succ k ih =>
    intro j hj
    simp only [zjBest]
    split_ifs with h
    · rcases Nat.lt_or_ge j (k+1) with hj' | hj'
      · exact (ih j (by omega)).trans h.le
      · rw [show j = k+1 by omega]
    · rcases Nat.lt_or_ge j (k+1) with hj' | hj'
      · exact ih j (by omega)
      · rw [show j = k+1 by omega]; exact not_lt.1 h

lemma zjBest_meas (k : ℕ) : Measurable (fun x : (ℕ → ℝ) × (ℕ → ℝ) => zjBest x.2 k) := by
  induction k with
  | zero => simp [zjBest]
  | succ k ih =>
    simp only [zjBest]
    refine Measurable.ite ?_ measurable_const ih
    have : {x : (ℕ → ℝ) × (ℕ → ℝ) | x.2 (zjBest x.2 k) < x.2 (k+1)} =
        ⋃ m : ℕ, ((fun x : (ℕ → ℝ) × (ℕ → ℝ) => zjBest x.2 k) ⁻¹' {m} ∩
          {x | x.2 m < x.2 (k+1)}) := by
      ext x; simp
    rw [this]
    refine MeasurableSet.iUnion fun m => (ih (measurableSet_singleton m)).inter ?_
    exact measurableSet_lt ((measurable_pi_apply m).comp measurable_snd)
      ((measurable_pi_apply (k+1)).comp measurable_snd)

noncomputable def zjTie : TieRule where
  choose n _ v := zjBest v (n-1)
  in_range n h v hn := by have := zjBest_le v (n-1); omega
  maximum n h v hn j hj := zjBest_max v (n-1) j (by omega)
  measurable n := zjBest_meas (n-1)

theorem solution : ¬ (∃ Ψ₁ Ψ₂ : ℝ, 0 < Ψ₁ ∧ 0 < Ψ₂ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (D : Model Ω) (_hA : Assumption1 D),
      ∀ (initD initT : Initialization D.M D.K) (tieD tieT : TieRule),
        (∃ ΔD ΔT : ℝ, IsLeast (positiveGaps D .decreasing) ΔD ∧
          IsLeast (positiveGaps D .threshold) ΔT ∧
          ∀ T : ℕ, 2 ≤ T →
            signedRegret D .decreasing initD tieD T ≤ Ψ₁ / ΔD * Real.log T / T ∧
            signedRegret D .threshold initT tieT T ≤ Ψ₁ / ΔT * Real.log T / T) ∧
        (∀ T : ℕ, 2 ≤ T →
          signedRegret D .decreasing initD tieD T ≤ Ψ₂ * Real.sqrt (Real.log T / T) ∧
          signedRegret D .threshold initT tieT T ≤ Ψ₂ * Real.sqrt (Real.log T / T))) := by
  rintro ⟨Ψ₁, Ψ₂, -, -, h⟩
  obtain ⟨⟨ΔD, ΔT, hD, -⟩, -⟩ := h Unit zjZero zj_A1 zjInit zjInit zjTie zjTie
  obtain ⟨hpos, w, -, hw⟩ := hD.1
  rw [zj_bench, zj_avg] at hw
  linarith
