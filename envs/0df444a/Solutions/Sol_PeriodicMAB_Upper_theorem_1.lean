-- Prove2me | solution 1 for PeriodicMAB.Upper.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:07:48.364968+00:00
-- url     : https://prove2.me/submissions/237aad87-e2ca-42db-a580-cb24792f1be1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Definitions.Def_PeriodicMAB_Upper_Policy
import Theorems.Thm_PeriodicMAB_Upper_lemma_11
import Theorems.Thm_PeriodicMAB_Upper_theorem_2

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
open PeriodicMAB.Upper

/-- pseudo-regret is between `0` and `T` under Assumption 1. -/
lemma pmab_regret_bounds {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (T : ℕ) (hA1 : Assumption1 μ T)
    (π : ℕ → Fin K) : 0 ≤ pseudoRegret μ T π ∧ pseudoRegret μ T π ≤ T := by
  have hne : (univ : Finset (Fin K)).Nonempty := univ_nonempty
  unfold pseudoRegret
  constructor
  · apply Finset.sum_nonneg
    intro t _
    have : μ (π t) t ≤ maxMean μ t := by
      unfold maxMean; rw [dif_pos hne]; exact Finset.le_sup' (fun k => μ k t) (mem_univ _)
    linarith
  · calc ∑ t ∈ Icc 1 T, (maxMean μ t - μ (π t) t) ≤ ∑ t ∈ Icc 1 T, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t ht
          rw [Finset.mem_Icc] at ht
          have h1 : maxMean μ t ≤ 1 := by
            unfold maxMean; rw [dif_pos hne]
            exact Finset.sup'_le _ _ (fun k _ => (hA1 k t ht.1 ht.2).2)
          have h2 := (hA1 (π t) t ht.1 ht.2).1
          linarith
      _ = T := by simp

lemma pmab_log7 : (1.9 : ℝ) ≤ Real.log 7 := by
  have h : Real.exp 19 < 7 ^ 10 := by
    have : Real.exp 19 = Real.exp 1 ^ 19 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h1 := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    calc Real.exp 1 ^ 19 < (2.7182818286 : ℝ) ^ 19 := by gcongr
      _ < 7 ^ 10 := by norm_num
  have : (19 : ℝ) < Real.log (7 ^ 10) := (Real.lt_log_iff_exp_lt (by norm_num)).mpr h
  rw [Real.log_pow] at this
  push_cast at this
  linarith

set_option maxHeartbeats 1000000 in
theorem solution (σ : ℝ≥0) (hσ : 0 < σ) (K : ℕ) [NeZero K] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℕ) (Tper : Fin K → ℕ) (μ : Fin K → ℕ → ℝ)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ),
        (∀ k, IsMinPeriod (μ k) (Tper k)) → Assumption1 μ T → IsSubGaussianNoise P ε σ →
        Assumption3 T (nPar T K) (gPar (nPar T K)) Tper →
        Assumption4 μ Tper σ (HPar (nPar T K)) (nPar T K) (gPar (nPar T K)) →
        ∃ Z : Ω → ℝ, Integrable Z P ∧
          (∀ ω, pseudoRegret μ T
            (twoStage μ ε σ (8 / T) (HPar (nPar T K)) T (nPar T K) (gPar (nPar T K)) ω) ≤ Z ω) ∧
          ∫ ω, Z ω ∂P ≤ C * Real.sqrt (T * effArms Tper * Real.log T ^ 2 *
            Real.log (T / effArms Tper)) := by
  obtain ⟨C1, hC1, hL11⟩ := lemma_11 σ hσ
  have hKpos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  set C2 : ℝ := 896 * K * Real.sqrt K with hC2
  have hC2pos : 0 < C2 := by positivity
  refine ⟨C1 + C2, by linarith, ?_⟩
  intro T Tper μ Ω _ P _ ε hper hA1 hε hA3 hA4
  set n := nPar T K with hn
  set g := gPar n with hg
  set H := HPar n with hH
  set d := effArms Tper with hd
  set R := Real.sqrt (T * d * Real.log T ^ 2 * Real.log (T / d)) with hR
  -- arithmetic facts from Assumption 3
  obtain ⟨hT4K, hg2, hsqg, hTk⟩ := hA3
  have hTk1 : ∀ k, (1 : ℝ) ≤ Tper k := fun k => by exact_mod_cast (hper k).1
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have h2gn : 2 * (g : ℝ) < n := by
    have := hTk 0
    have h1 := hTk1 0
    have : (1 : ℝ) < n / (2 * g) := lt_of_le_of_lt h1 this
    rwa [one_lt_div (by positivity)] at this
  have hng : (n : ℝ) ≤ (g : ℝ) ^ 2 := by
    have := Real.sqrt_le_sqrt (le_refl (n:ℝ))
    have h0 : (0:ℝ) ≤ n := by positivity
    calc (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ (g : ℝ) ^ 2 := by gcongr
  have hn7 : (7 : ℝ) ≤ n := by
    have h2gn' : 2 * g < n := by exact_mod_cast h2gn
    have hng' : n ≤ g ^ 2 := by exact_mod_cast hng
    have : 7 ≤ n := by
      by_contra hc
      push Not at hc
      have : g ≤ 2 := by omega
      have : g = 2 := by omega
      subst_vars
      nlinarith
    exact_mod_cast this
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : (1.9 : ℝ) ≤ Real.log n :=
    le_trans pmab_log7 (Real.log_le_log (by norm_num) hn7)
  -- n ≤ √(T/K) < n + 1
  have hsqrtTK : Real.sqrt ((T : ℝ) / K) < n + 1 := Nat.lt_floor_add_one _
  have hn_le : (n : ℝ) ≤ Real.sqrt ((T : ℝ) / K) := Nat.floor_le (Real.sqrt_nonneg _)
  have hTpos : (0 : ℝ) < T := by
    have : (4 * K : ℝ) < T := by exact_mod_cast hT4K
    linarith
  have hKn2 : (K : ℝ) * n ^ 2 ≤ T := by
    have : (n : ℝ) ^ 2 ≤ T / K := by
      calc (n : ℝ) ^ 2 ≤ Real.sqrt ((T : ℝ) / K) ^ 2 := by gcongr
        _ = (T : ℝ) / K := Real.sq_sqrt (by positivity)
    rwa [le_div_iff₀ hKR, mul_comm] at this
  -- bounds on d
  have hd1 : (1 : ℝ) ≤ d := by
    rw [hd, effArms]; push_cast
    calc (1 : ℝ) ≤ Tper 0 := hTk1 0
      _ ≤ ∑ k, (Tper k : ℝ) :=
        Finset.single_le_sum (f := fun k => (Tper k : ℝ)) (fun k _ => by positivity) (mem_univ _)
  have hdlt : (d : ℝ) ≤ K * n / 4 := by
    rw [hd, effArms]; push_cast
    calc ∑ k, (Tper k : ℝ) ≤ ∑ _k : Fin K, (n : ℝ) / (2 * g) :=
          Finset.sum_le_sum (fun k _ => (hTk k).le)
      _ = K * (n / (2 * g)) := by simp
      _ ≤ K * (n / 4) := by
          gcongr; linarith
      _ = K * n / 4 := by ring
  have he : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
    have h49 : (49 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have : (49 : ℝ) ≤ T := by nlinarith
    linarith
  have hlogTd : 1 ≤ Real.log (T / d) := by
    have hdpos : (0 : ℝ) < d := by linarith
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hdpos]
    nlinarith
  have hRge : Real.sqrt T ≤ R := by
    rw [hR]
    apply Real.sqrt_le_sqrt
    have h1 : (1 : ℝ) ≤ Real.log T ^ 2 := by nlinarith
    have : (1 : ℝ) ≤ d * Real.log T ^ 2 * Real.log (T / d) := by
      have := mul_le_mul h1 hlogTd (by norm_num) (by positivity)
      nlinarith
    nlinarith
  -- failure probability bound
  have hHpos : 0 < H := by
    rw [hH, HPar]; apply Real.sqrt_pos.mpr; linarith
  have hH2 : H ^ 2 = 1 + Real.log n := by
    rw [hH, HPar, Real.sq_sqrt]; linarith
  set F : ℝ := 48 * K / (n : ℝ) ^ (H ^ 2 - 1) + 200 * K / (n : ℝ) ^ (0.867 * H ^ 2 - 1) +
        200 * K / (n : ℝ) ^ (0.6934 * H ^ 2 - 1) with hF
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hpow : ∀ c : ℝ, 1 ≤ c * H ^ 2 - 1 → (n : ℝ) ≤ (n : ℝ) ^ (c * H ^ 2 - 1) := by
    intro c hc
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ (c * H ^ 2 - 1) := Real.rpow_le_rpow_of_exponent_le hn1 hc
  have hterm : ∀ (a c : ℝ), 0 ≤ a → 1 ≤ c * H ^ 2 - 1 →
      a * K / (n : ℝ) ^ (c * H ^ 2 - 1) ≤ a * K / n := by
    intro a c ha hc
    apply div_le_div_of_nonneg_left (by positivity) hnpos (hpow c hc)
  have hF0 : 0 ≤ F := by positivity
  have hFle : F ≤ 448 * K / n := by
    have e1 := hterm 48 1 (by norm_num) (by rw [hH2]; linarith)
    have e2 := hterm 200 0.867 (by norm_num) (by rw [hH2]; norm_num; linarith)
    have e3 := hterm 200 0.6934 (by norm_num) (by rw [hH2]; norm_num; linarith)
    rw [one_mul] at e1
    rw [hF]
    calc _ ≤ 48 * (K : ℝ) / n + 200 * (K : ℝ) / n + 200 * (K : ℝ) / n := by linarith
      _ = 448 * (K : ℝ) / n := by ring
  have hTn : (T : ℝ) / n ≤ 2 * Real.sqrt K * Real.sqrt T := by
    have hs : Real.sqrt ((T : ℝ) / K) = Real.sqrt T / Real.sqrt K := Real.sqrt_div' _ hKR.le
    rw [hs, div_lt_iff₀ (Real.sqrt_pos.mpr hKR)] at hsqrtTK
    have hsT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hTpos.le
    rw [div_le_iff₀ hnpos]
    have hsK := Real.sqrt_nonneg (K : ℝ)
    have hsTn := Real.sqrt_nonneg (T : ℝ)
    calc (T : ℝ) = Real.sqrt T * Real.sqrt T := hsT.symm
      _ ≤ Real.sqrt T * ((n + 1) * Real.sqrt K) := by gcongr
      _ ≤ Real.sqrt T * ((2 * n) * Real.sqrt K) := by gcongr; linarith
      _ = 2 * Real.sqrt K * Real.sqrt T * n := by ring
  have hTF : (T : ℝ) * F ≤ C2 * R := by
    calc (T : ℝ) * F ≤ T * (448 * (K : ℝ) / n) := mul_le_mul_of_nonneg_left hFle hTpos.le
      _ = 448 * (K : ℝ) * (T / n) := by ring
      _ ≤ 448 * (K : ℝ) * (2 * Real.sqrt K * Real.sqrt T) :=
          mul_le_mul_of_nonneg_left hTn (by positivity)
      _ = C2 * Real.sqrt T := by rw [hC2]; ring
      _ ≤ C2 * R := mul_le_mul_of_nonneg_left hRge hC2pos.le
  -- the two milestones
  obtain ⟨Z1, hZ1int, hZ1ge, hZ1int_le⟩ :=
    hL11 K T Tper μ P ε hper hA1 hε ⟨hT4K, hg2, hsqg, hTk⟩
  have hT2 := theorem_2 P ε σ hσ hε μ Tper T n g H hHpos hper ⟨hT4K, hg2, hsqg, hTk⟩ hA4
  set Λ := eventLambda μ ε σ H n g Tper with hΛ
  set M := toMeasurable P Λᶜ with hM
  have hMmeas : MeasurableSet M := measurableSet_toMeasurable _ _
  have hPM : P.real M ≤ F := by
    rw [measureReal_def, hM, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hF0 hT2
  refine ⟨fun ω => Z1 ω + M.indicator (fun _ => (T : ℝ)) ω,
    hZ1int.add ((integrable_const _).indicator hMmeas), ?_, ?_⟩
  · intro ω
    have hZ1nn : 0 ≤ Z1 ω := le_trans (pmab_regret_bounds μ T hA1 _).1 (hZ1ge ω)
    by_cases hω : ω ∈ Λ
    · have heq : twoStage μ ε σ (8 / T) H T n g ω = oracle μ ε σ (8 / T) T n Tper ω := by
        unfold twoStage oracle
        have : (fun k => estPeriod μ ε σ H n g k ω) = Tper := funext hω
        rw [this]
      beta_reduce
      rw [heq]
      have : 0 ≤ M.indicator (fun _ => (T : ℝ)) ω := by
        unfold Set.indicator; split_ifs <;> positivity
      linarith [hZ1ge ω]
    · have hωM : ω ∈ M := subset_toMeasurable _ _ hω
      beta_reduce
      rw [Set.indicator_of_mem hωM]
      linarith [(pmab_regret_bounds μ T hA1 (twoStage μ ε σ (8 / T) H T n g ω)).2]
  · rw [integral_add hZ1int ((integrable_const _).indicator hMmeas),
      integral_indicator_const _ hMmeas, smul_eq_mul]
    have : P.real M * T ≤ F * T := by gcongr
    calc _ ≤ C1 * R + F * T := by linarith
      _ ≤ C1 * R + C2 * R := by linarith
      _ = (C1 + C2) * R := by ring
