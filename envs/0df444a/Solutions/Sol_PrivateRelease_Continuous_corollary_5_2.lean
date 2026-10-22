-- Prove2me | solution 1 for PrivateRelease.Continuous.corollary_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T09:17:40.269279+00:00
-- url     : https://prove2.me/submissions/13a49e7a-bcdb-46e5-98f8-95fafba6c082

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivateRelease_Continuous_Queries

set_option autoImplicit false

open MeasureTheory PrivLearn.Generic

namespace Cor52Aux

lemma step {n : ℕ} {O : Type} [MeasurableSpace O] (A : (Fin n → ℝ) → Measure O) (ε : ℝ)
    (hε : 0 ≤ ε) (hdp : IsDP A ε) (z z' : Fin n → ℝ) (S : Set O) (hS : MeasurableSet S)
    (k : ℕ) (hk : k < n) :
    A (fun i => if i.val < k then z' i else z i) S ≤
      ENNReal.ofReal (Real.exp ε) * A (fun i => if i.val < k + 1 then z' i else z i) S := by
  by_cases h : z ⟨k, hk⟩ = z' ⟨k, hk⟩
  · have heq : (fun i : Fin n => if i.val < k then z' i else z i) =
        (fun i => if i.val < k + 1 then z' i else z i) := by
      funext i
      by_cases h1 : i.val < k
      · have : i.val < k + 1 := by omega
        simp [h1, this]
      · by_cases h2 : i.val = k
        · have hi : i = ⟨k, hk⟩ := Fin.ext h2
          subst hi
          simp [h]
        · have : ¬ i.val < k + 1 := by omega
          simp [h1, this]
    rw [heq]
    have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (Real.exp ε) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hε)
    calc _ = 1 * A (fun i => if i.val < k + 1 then z' i else z i) S := (one_mul _).symm
      _ ≤ _ := by gcongr
  · apply hdp _ _ _ S hS
    refine ⟨⟨k, hk⟩, ?_, ?_⟩
    · simp [h]
    · intro j hj
      have : j.val ≠ k := fun e => hj (Fin.ext e)
      by_cases h1 : j.val < k
      · have : j.val < k + 1 := by omega
        simp [h1, this]
      · have : ¬ j.val < k + 1 := by omega
        simp [h1, this]

lemma chain {n : ℕ} {O : Type} [MeasurableSpace O] (A : (Fin n → ℝ) → Measure O) (ε : ℝ)
    (hε : 0 ≤ ε) (hdp : IsDP A ε) (z z' : Fin n → ℝ) (S : Set O) (hS : MeasurableSet S) :
    A z S ≤ ENNReal.ofReal (Real.exp ε) ^ n * A z' S := by
  have key : ∀ k, k ≤ n → A z S ≤ ENNReal.ofReal (Real.exp ε) ^ k *
      A (fun i => if i.val < k then z' i else z i) S := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      calc A z S ≤ ENNReal.ofReal (Real.exp ε) ^ k *
            A (fun i => if i.val < k then z' i else z i) S := ih (by omega)
        _ ≤ ENNReal.ofReal (Real.exp ε) ^ k * (ENNReal.ofReal (Real.exp ε) *
            A (fun i => if i.val < k + 1 then z' i else z i) S) := by
          gcongr
          exact step A ε hε hdp z z' S hS k (by omega)
        _ = _ := by rw [pow_succ, mul_assoc]
  have h := key n le_rfl
  have : (fun i : Fin n => if i.val < n then z' i else z i) = z' := by
    funext i; simp [i.isLt]
  rwa [this] at h

end Cor52Aux

open MeasureTheory PrivLearn.Generic PrivateRelease.Continuous in
theorem solution (n : ℕ) (O : Type) [MeasurableSpace O] (A : (Fin n → ℝ) → Measure O)
    (ans : O → ℝ → ℝ → ℝ) (ε α δ : ℝ)
    (hn : 1 ≤ n) (hε : 0 ≤ ε) (hα : α < 1 / 2) (hδ : δ < 1 / 2)
    (hA : ∀ z, IsProbabilityMeasure (A z)) (hans : ∀ a b : ℝ, Measurable fun o => ans o a b)
    (hdp : IsDP A ε) :
    ¬ UsefulIntervals A ans α δ := by
  intro hU
  classical
  let zk : ℕ → (Fin n → ℝ) := fun k _ => (k : ℝ)
  let E : ℕ → Set O := fun k => {o | |ans o k k - 1| ≤ α} ∩
    ⋂ j : ℕ, ⋂ (_ : j ≠ k), {o | |ans o j j| ≤ α}
  have hEm : ∀ k, MeasurableSet (E k) := by
    intro k
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le
        (continuous_abs.measurable.comp ((hans _ _).sub measurable_const)) measurable_const
    · refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
      exact measurableSet_le (continuous_abs.measurable.comp (hans _ _)) measurable_const
  have hdisj : ∀ k l : ℕ, k ≠ l → Disjoint (E k) (E l) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro o hk hl
    have h1 : |ans o k k - 1| ≤ α := hk.1
    have h2 : |ans o k k| ≤ α := by
      have := hl.2
      simp only [Set.mem_iInter] at this
      exact this k hkl
    rw [abs_le] at h1 h2
    linarith [h1.1, h1.2, h2.1, h2.2]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq1 : ∀ k : ℕ, intervalQuery (k : ℝ) k (zk k) = 1 := by
    intro k
    unfold intervalQuery
    rw [Finset.filter_true_of_mem (fun i _ => ⟨le_rfl, le_rfl⟩)]
    rw [Finset.card_univ, Fintype.card_fin]
    exact div_self hn'
  have hq0 : ∀ j k : ℕ, j ≠ k → intervalQuery (j : ℝ) j (zk k) = 0 := by
    intro j k hjk
    have hne : ¬ ((j : ℝ) ≤ k ∧ (k : ℝ) ≤ j) := fun h =>
      hjk (by exact_mod_cast le_antisymm h.1 h.2)
    unfold intervalQuery
    rw [Finset.filter_false_of_mem (fun i _ => hne)]
    simp
  have hsub : ∀ k : ℕ, {o | ∀ a b : ℝ, a ≤ b → |ans o a b - intervalQuery a b (zk k)| ≤ α}
      ⊆ E k := by
    intro k o ho
    refine ⟨?_, ?_⟩
    · have := ho k k le_rfl
      rw [hq1 k] at this
      exact this
    · simp only [Set.mem_iInter]
      intro j hjk
      have := ho j j le_rfl
      rw [hq0 j k hjk, sub_zero] at this
      exact this
  set C : ENNReal := ENNReal.ofReal (Real.exp ε) ^ n with hC
  have hk : ∀ k : ℕ, ENNReal.ofReal (1 - δ) ≤ C * A (zk 0) (E k) := by
    intro k
    calc ENNReal.ofReal (1 - δ) ≤ A (zk k) _ := hU (zk k)
      _ ≤ A (zk k) (E k) := measure_mono (hsub k)
      _ ≤ C * A (zk 0) (E k) := Cor52Aux.chain A ε hε hdp _ _ _ (hEm k)
  set M : ℝ := Real.exp ε ^ n with hM
  have hM0 : 0 < M := pow_pos (Real.exp_pos ε) n
  set K : ℕ := Nat.ceil (2 * M) + 1 with hK
  have hKr : 2 * M < (K : ℝ) := by
    have := Nat.le_ceil (2 * M)
    rw [hK]; push_cast; linarith
  have hsum : ∑ k ∈ Finset.range K, ENNReal.ofReal (1 - δ) ≤
      ∑ k ∈ Finset.range K, C * A (zk 0) (E k) := Finset.sum_le_sum (fun k _ => hk k)
  have hpd : Set.PairwiseDisjoint (↑(Finset.range K)) E := fun k _ l _ hkl => hdisj k l hkl
  rw [← Finset.mul_sum, ← measure_biUnion_finset hpd (fun k _ => hEm k)] at hsum
  have := hA (zk 0)
  have hle1 : A (zk 0) (⋃ k ∈ Finset.range K, E k) ≤ 1 := prob_le_one
  have hCM : C = ENNReal.ofReal M := by
    rw [hC, hM, ENNReal.ofReal_pow (Real.exp_pos ε).le]
  have hfin : ((K : ENNReal) * ENNReal.ofReal (1 - δ)) ≤ ENNReal.ofReal M := by
    calc ((K : ENNReal) * ENNReal.ofReal (1 - δ))
        = ∑ k ∈ Finset.range K, ENNReal.ofReal (1 - δ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ C * A (zk 0) (⋃ k ∈ Finset.range K, E k) := hsum
      _ ≤ C * 1 := by gcongr
      _ = ENNReal.ofReal M := by rw [mul_one, hCM]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff hM0.le] at hfin
  have hKpos : (0 : ℝ) < K := by linarith
  have : 0 < (K : ℝ) * (1 / 2 - δ) := mul_pos hKpos (by linarith)
  nlinarith
