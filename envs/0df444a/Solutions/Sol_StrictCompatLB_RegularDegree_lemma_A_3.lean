-- Prove2me | solution 1 for StrictCompatLB.RegularDegree.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T11:58:07.026699+00:00
-- url     : https://prove2.me/submissions/68f32f39-ceaf-4b56-9562-3cfabcf93df3

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
import Definitions.Def_StrictCompatLB_RegularDegree_RandomServerRegular
import Theorems.Thm_StrictCompatLB_RegularDegree_lemma_A_2

open Finset Filter MeasureTheory Topology

namespace StrictCompatLB.RegularDegree.A3aux

open StrictCompatLB.MeanField

lemma double_count (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (U : Finset (Fin N)) (X : Finset (Fin (M N))) :
    ∑ w ∈ X, (nbrW M G N w ∩ U).card = ∑ v ∈ U, (nbrV M G N v ∩ X).card := by
  classical
  have h1 : ∀ w, (nbrW M G N w ∩ U) = U.filter (fun v => (v, w) ∈ G N) := by
    intro w; ext v; simp [nbrW, and_comm]
  have h2 : ∀ v, (nbrV M G N v ∩ X) = X.filter (fun w => (v, w) ∈ G N) := by
    intro v; ext w; simp [nbrV, and_comm]
  simp_rw [h1, h2, Finset.card_filter]
  exact Finset.sum_comm

end StrictCompatLB.RegularDegree.A3aux

open StrictCompatLB.RegularDegree StrictCompatLB.MeanField StrictCompatLB.RegularDegree.A3aux in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M c : ℕ → ℕ) (hc_pos : ∀ N, 1 ≤ c N) (hcM : ∀ N, c N ≤ M N)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (hc : Tendsto (fun N : ℕ => (c N : ℝ)) atTop atTop)
    (hNcM : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / (M N : ℝ)) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀,
      ((lowDegreeDispatchers M c (randomGraph M adj ω) ε N).card : ℝ) ≤ δ * (M N : ℝ) := by
  classical
  set x : ℝ := min (ε / 3) (1 / 4) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ ε / 3 := min_le_left _ _
  have hx2 : x ≤ 1 / 4 := min_le_right _ _
  filter_upwards [lemma_A_2 P M c hc_pos hcM adj hadj hc hNcM x hx0 (by linarith) x hx0
    (by linarith) δ hδ] with ω hω
  obtain ⟨N₀, hN₀1, hN₀⟩ := hω
  refine ⟨N₀, hN₀1, fun N hN => ?_⟩
  set G := randomGraph M adj ω
  set A := lowDegreeDispatchers M c G ε N
  by_contra hcon
  push_neg at hcon
  have hB := hN₀ N hN A hcon.le
  have hNpos : (0:ℝ) < N := by
    have : 1 ≤ N := le_trans hN₀1 hN
    exact_mod_cast this
  have hMpos : (0:ℝ) < M N := by
    have := (hc_pos N).trans (hcM N); exact_mod_cast (show 0 < M N by omega)
  have hcpos : (0:ℝ) < c N := by have := hc_pos N; exact_mod_cast (show 0 < c N by omega)
  have hApos : (0:ℝ) < A.card := lt_of_le_of_lt (by positivity) hcon
  set B := badServers M c G x N A
  -- upper bound on edges
  have hup : (∑ w ∈ A, ((nbrW M G N w ∩ Finset.univ).card : ℝ))
      ≤ A.card * ((1 - ε) * ((N : ℝ) * c N / M N)) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro w hw
    have := (Finset.mem_filter.mp hw).2
    simpa using this
  -- lower bound on edges
  have hlow : ((N : ℝ) - B.card) * ((1 - x) * (c N * A.card / M N))
      ≤ ∑ v ∈ (Finset.univ : Finset (Fin N)), ((nbrV M G N v ∩ A).card : ℝ) := by
    have hsplit : ∑ v ∈ (Finset.univ : Finset (Fin N)), ((nbrV M G N v ∩ A).card : ℝ)
        ≥ ∑ v ∈ (Finset.univ \ B), ((nbrV M G N v ∩ A).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => by positivity)
    have hcardc : ((Finset.univ \ B).card : ℝ) = N - B.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub (by simpa using Finset.card_le_univ B)]
    have hgood : ∑ v ∈ (Finset.univ \ B), ((1 - x) * (c N * A.card / M N))
        ≤ ∑ v ∈ (Finset.univ \ B), ((nbrV M G N v ∩ A).card : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvB : v ∉ B := (Finset.mem_sdiff.mp hv).2
      simp only [B, badServers, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hvB
      have := neg_abs_le (((nbrV M G N v ∩ A).card : ℝ) - c N * A.card / M N)
      have e1 : x * c N * A.card / M N = x * (c N * A.card / M N) := by ring
      rw [e1] at hvB
      nlinarith
    rw [Finset.sum_const, nsmul_eq_mul, hcardc] at hgood
    linarith
  have hdc := double_count M G N Finset.univ A
  have hdcR : (∑ w ∈ A, ((nbrW M G N w ∩ Finset.univ).card : ℝ))
      = ∑ v ∈ (Finset.univ : Finset (Fin N)), ((nbrV M G N v ∩ A).card : ℝ) := by
    exact_mod_cast hdc
  -- combine
  have key : ((N : ℝ) - B.card) * ((1 - x) * (c N * A.card / M N))
      ≤ A.card * ((1 - ε) * ((N : ℝ) * c N / M N)) := by linarith
  have hB' : (B.card : ℝ) ≤ x * N := hB
  set t : ℝ := c N * A.card / M N with ht
  have htpos : 0 < t := by positivity
  have e2 : (A.card : ℝ) * ((1 - ε) * ((N : ℝ) * c N / M N)) = (1 - ε) * N * t := by
    rw [ht]; ring
  rw [e2] at key
  have h3 : ((N : ℝ) - x * N) * ((1 - x) * t) ≤ ((N : ℝ) - B.card) * ((1 - x) * t) := by
    apply mul_le_mul_of_nonneg_right (by linarith)
    have : 0 ≤ 1 - x := by linarith
    positivity
  have h4 : (1 - ε) * N * t < ((N : ℝ) - x * N) * ((1 - x) * t) := by
    have : ((N : ℝ) - x * N) * ((1 - x) * t) = (1 - x) ^ 2 * (N * t) := by ring
    rw [this]
    have hNt : 0 < (N : ℝ) * t := by positivity
    have : (1 - ε) * N * t = (1 - ε) * (N * t) := by ring
    rw [this]
    apply mul_lt_mul_of_pos_right _ hNt
    nlinarith
  linarith
