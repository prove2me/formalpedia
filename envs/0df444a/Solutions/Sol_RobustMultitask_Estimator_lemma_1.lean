-- Prove2me | solution 1 for RobustMultitask.Estimator.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T14:17:54.55245+00:00
-- url     : https://prove2.me/submissions/ba52828e-eed6-4dff-bf2a-9915be5ddffc

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_Model

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal
open RobustMultitask.Estimator

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ)
    (hmodel : IsMultitaskModel P n X β βdag s σ ε) (j : Fin N) (lam : ℝ) (hlam : 0 < lam) :
    P {ω | ¬ ((2 / (n j : ℝ)) * linf ((X j)ᵀ *ᵥ (fun k => ε j k ω)) ≤ lam / 2)}
      ≤ ENNReal.ofReal
          (2 * d * Real.exp (-(lam ^ 2 * (n j : ℝ)) / (32 * (σ j : ℝ) ^ 2))) := by
  have hn : (0 : ℝ) < n j := by exact_mod_cast hmodel.pos_n j
  have hσ : (0 : ℝ) < σ j := by exact_mod_cast hmodel.pos_σ j
  set t : ℝ := lam * n j / 4 with ht
  have ht0 : 0 ≤ t := by positivity
  -- the noise of task `j` is an independent family
  have hind : iIndepFun (fun k : Fin (n j) => ε j k) P :=
    hmodel.indep.precomp (g := fun k : Fin (n j) => (⟨j, k⟩ : Σ j : Fin N, Fin (n j)))
      (fun a b h => by simpa using h)
  -- each coordinate of `Xᵀ ε` is subgaussian with variance proxy `σ_j² n_j`
  have hsub : ∀ i : Fin d, HasSubgaussianMGF (fun ω => ((X j)ᵀ *ᵥ (fun k => ε j k ω)) i)
      (σ j ^ 2 * (n j : ℝ≥0)) P := by
    intro i
    have hind' : iIndepFun (fun k : Fin (n j) => fun ω => X j k i * ε j k ω) P :=
      hind.comp (fun k x => X j k i * x) (fun k => measurable_const.mul measurable_id)
    have := HasSubgaussianMGF.sum_of_iIndepFun hind' (s := Finset.univ)
      (c := fun k => Real.toNNReal (X j k i ^ 2) * σ j ^ 2)
      (fun k _ => by
        have h := (hmodel.subgaussian j k).const_mul (X j k i)
        convert h using 2
        apply NNReal.eq
        simp [Real.coe_toNNReal _ (sq_nonneg (X j k i))]
        rfl)
    have hc : (∑ k, Real.toNNReal (X j k i ^ 2) * σ j ^ 2) = σ j ^ 2 * (n j : ℝ≥0) := by
      apply NNReal.eq
      have hs := hmodel.standardized j i
      have hsum : ∑ k, X j k i ^ 2 = n j := by
        field_simp at hs; linarith
      rw [NNReal.coe_sum]
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_pow,
        NNReal.coe_natCast]
      rw [← Finset.sum_mul, hsum]; ring
    rw [← hc]
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp [mulVec, dotProduct, transpose_apply]
  have hproxy : ∀ i : Fin d,
      (((σ j ^ 2 * (n j : ℝ≥0) : ℝ≥0)) : ℝ) = (σ j : ℝ) ^ 2 * n j := by
    intro i; push_cast; ring
  have hexp : -t ^ 2 / (2 * ((σ j : ℝ) ^ 2 * n j))
      = -(lam ^ 2 * (n j : ℝ)) / (32 * (σ j : ℝ) ^ 2) := by
    rw [ht]; field_simp; ring
  -- one-sided tail bounds
  have htail : ∀ i : Fin d,
      P {ω | t ≤ ((X j)ᵀ *ᵥ (fun k => ε j k ω)) i}
        ≤ ENNReal.ofReal (Real.exp (-(lam ^ 2 * (n j : ℝ)) / (32 * (σ j : ℝ) ^ 2))) := by
    intro i
    rw [← ofReal_measureReal, ← hexp, ← hproxy i]
    exact ENNReal.ofReal_le_ofReal ((hsub i).measure_ge_le ht0)
  have htail' : ∀ i : Fin d,
      P {ω | t ≤ -((X j)ᵀ *ᵥ (fun k => ε j k ω)) i}
        ≤ ENNReal.ofReal (Real.exp (-(lam ^ 2 * (n j : ℝ)) / (32 * (σ j : ℝ) ^ 2))) := by
    intro i
    rw [← ofReal_measureReal, ← hexp, ← hproxy i]
    exact ENNReal.ofReal_le_ofReal ((hsub i).neg.measure_ge_le ht0)
  -- the bad event is covered by the coordinate tails
  have hcover : {ω | ¬ ((2 / (n j : ℝ)) * linf ((X j)ᵀ *ᵥ (fun k => ε j k ω)) ≤ lam / 2)}
      ⊆ ⋃ i : Fin d, ({ω | t ≤ ((X j)ᵀ *ᵥ (fun k => ε j k ω)) i}
          ∪ {ω | t ≤ -((X j)ᵀ *ᵥ (fun k => ε j k ω)) i}) := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hc
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or,
      not_le] at hc
    apply hω
    have hl : linf ((X j)ᵀ *ᵥ (fun k => ε j k ω)) ≤ t := by
      unfold linf
      refine Real.iSup_le (fun i => ?_) ht0
      rcases hc i with ⟨h1, h2⟩
      rw [abs_le]; constructor <;> linarith
    calc (2 / (n j : ℝ)) * linf ((X j)ᵀ *ᵥ (fun k => ε j k ω)) ≤ (2 / (n j : ℝ)) * t := by
          gcongr
      _ = lam / 2 := by rw [ht]; field_simp; ring
  calc _ ≤ P (⋃ i : Fin d, ({ω | t ≤ ((X j)ᵀ *ᵥ (fun k => ε j k ω)) i}
          ∪ {ω | t ≤ -((X j)ᵀ *ᵥ (fun k => ε j k ω)) i})) := measure_mono hcover
    _ ≤ ∑ i : Fin d, P ({ω | t ≤ ((X j)ᵀ *ᵥ (fun k => ε j k ω)) i}
          ∪ {ω | t ≤ -((X j)ᵀ *ᵥ (fun k => ε j k ω)) i}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin d, (ENNReal.ofReal (Real.exp (-(lam ^ 2 * (n j : ℝ)) / (32 * (σ j : ℝ) ^ 2)))
          + ENNReal.ofReal (Real.exp (-(lam ^ 2 * (n j : ℝ)) / (32 * (σ j : ℝ) ^ 2)))) := by
        gcongr with i
        exact (measure_union_le _ _).trans (add_le_add (htail i) (htail' i))
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_add
          (by positivity) (by positivity), nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
