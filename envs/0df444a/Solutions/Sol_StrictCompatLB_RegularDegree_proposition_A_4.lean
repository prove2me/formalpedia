-- Prove2me | solution 1 for StrictCompatLB.RegularDegree.proposition_A_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T12:03:11.081987+00:00
-- url     : https://prove2.me/submissions/49e68f95-7217-47d2-99ab-d71cc7c339b8

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions
import Definitions.Def_StrictCompatLB_RegularDegree_RandomServerRegular
import Theorems.Thm_StrictCompatLB_RegularDegree_lemma_A_2
import Theorems.Thm_StrictCompatLB_RegularDegree_lemma_A_3

open Finset Filter MeasureTheory Topology

namespace StrictCompatLB.RegularDegree.A4aux

open StrictCompatLB.MeanField StrictCompatLB.RegularDegree

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

/-- The over-connection bound: a set `X` of non-low-degree dispatchers that are all
over-connected to `U` by `ε` is small. -/
lemma over_bound (M c : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (hN : 0 < N) (hc : 0 < c N) (hM : 0 < M N)
    (hreg : ∀ v : Fin N, (nbrV M G N v).card = c N)
    (ε t : ℝ) (ht0 : 0 < t) (htε : t ≤ ε) (ht1 : t ≤ 1)
    (hA2 : ∀ X : Finset (Fin (M N)), t / 3 * (M N : ℝ) ≤ (X.card : ℝ) →
        ((badServers M c G (t / 4) N X).card : ℝ) ≤ t ^ 2 / 48 * (N : ℝ))
    (U : Finset (Fin N)) (X : Finset (Fin (M N)))
    (hXA : ∀ w ∈ X, w ∉ lowDegreeDispatchers M c G (t / 4) N)
    (hXU : ∀ w ∈ X, ((nbrW M G N w).card : ℝ) * ((U.card : ℝ) / N + ε)
        ≤ ((nbrW M G N w ∩ U).card : ℝ)) :
    (X.card : ℝ) ≤ t / 3 * (M N : ℝ) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hB := hA2 X hcon.le
  set B := badServers M c G (t / 4) N X
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hMr : (0:ℝ) < M N := by exact_mod_cast hM
  have hcr : (0:ℝ) < c N := by exact_mod_cast hc
  set μ : ℝ := (N : ℝ) * c N / M N with hμ
  have hμpos : 0 < μ := by positivity
  set u : ℝ := (U.card : ℝ) / N with hu
  have hu0 : 0 ≤ u := by positivity
  have hUN : (U.card : ℝ) ≤ N := by
    have := Finset.card_le_univ U; simp at this; exact_mod_cast this
  -- lower bound on s
  have hlow : (X.card : ℝ) * ((1 - t / 4) * μ * (u + ε))
      ≤ ∑ w ∈ X, ((nbrW M G N w ∩ U).card : ℝ) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro w hw
    have h1 := hXA w hw
    simp only [lowDegreeDispatchers, Finset.mem_filter, Finset.mem_univ, true_and,
      not_le] at h1
    have h2 := hXU w hw
    have : (1 - t / 4) * μ * (u + ε) ≤ ((nbrW M G N w).card : ℝ) * (u + ε) := by
      apply mul_le_mul_of_nonneg_right h1.le (by linarith)
    linarith
  -- upper bound on s
  have hup : ∑ v ∈ U, ((nbrV M G N v ∩ X).card : ℝ)
      ≤ (c N : ℝ) * B.card + (U.card : ℝ) * ((1 + t / 4) * (c N * X.card / M N)) := by
    rw [← Finset.sum_filter_add_sum_filter_not U (fun v => v ∈ B)]
    apply add_le_add
    · calc ∑ v ∈ U.filter (fun v => v ∈ B), ((nbrV M G N v ∩ X).card : ℝ)
          ≤ ∑ v ∈ U.filter (fun v => v ∈ B), (c N : ℝ) := by
            apply Finset.sum_le_sum
            intro v _
            have := Finset.card_le_card (Finset.inter_subset_left (s₁ := nbrV M G N v) (s₂ := X))
            rw [hreg v] at this
            exact_mod_cast this
        _ = (U.filter (fun v => v ∈ B)).card * (c N : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (B.card : ℝ) * c N := by
            apply mul_le_mul_of_nonneg_right _ hcr.le
            have : U.filter (fun v => v ∈ B) ⊆ B := fun v hv => (Finset.mem_filter.mp hv).2
            exact_mod_cast Finset.card_le_card this
        _ = (c N : ℝ) * B.card := by ring
    · calc ∑ v ∈ U.filter (fun v => v ∉ B), ((nbrV M G N v ∩ X).card : ℝ)
          ≤ ∑ v ∈ U.filter (fun v => v ∉ B), ((1 + t / 4) * (c N * X.card / M N)) := by
            apply Finset.sum_le_sum
            intro v hv
            have hvB := (Finset.mem_filter.mp hv).2
            simp only [B, badServers, Finset.mem_filter, Finset.mem_univ, true_and,
              not_le] at hvB
            have := le_abs_self (((nbrV M G N v ∩ X).card : ℝ) - c N * X.card / M N)
            have e1 : t / 4 * c N * X.card / M N = t / 4 * (c N * X.card / M N) := by ring
            rw [e1] at hvB
            nlinarith
        _ = (U.filter (fun v => v ∉ B)).card * ((1 + t / 4) * (c N * X.card / M N)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (U.card : ℝ) * ((1 + t / 4) * (c N * X.card / M N)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have hdc : (∑ w ∈ X, ((nbrW M G N w ∩ U).card : ℝ))
      = ∑ v ∈ U, ((nbrV M G N v ∩ X).card : ℝ) := by
    exact_mod_cast double_count M G N U X
  have key := hlow.trans (hdc ▸ hup)
  -- algebra
  set x : ℝ := (X.card : ℝ)
  set b : ℝ := (B.card : ℝ)
  set n : ℝ := (N : ℝ)
  set m : ℝ := (M N : ℝ)
  set C : ℝ := (c N : ℝ)
  set k : ℝ := (U.card : ℝ)
  have hb : b ≤ t ^ 2 / 48 * n := hB
  have e3 : x * ((1 - t / 4) * μ * (u + ε)) = (C / m) * (x * (1 - t / 4) * (k + ε * n)) := by
    rw [hμ, hu]; field_simp
  have e4 : C * b + k * ((1 + t / 4) * (C * x / m)) = (C / m) * (b * m + k * (1 + t / 4) * x) := by
    field_simp
  rw [e3, e4] at key
  have hCm : 0 < C / m := by positivity
  have key2 : x * (1 - t / 4) * (k + ε * n) ≤ b * m + k * (1 + t / 4) * x :=
    le_of_mul_le_mul_left key hCm
  have hx0 : 0 ≤ x := by positivity
  have hk0 : 0 ≤ k := by positivity
  -- x * (n * t / 4) ≤ b * m
  have key3 : x * (n * t / 4) ≤ b * m := by
    have hε' : 3 / 4 * t ≤ (1 - t / 4) * ε := by nlinarith
    have hn0 : 0 ≤ n := hNr.le
    have h5 : 3 / 4 * t * n ≤ (1 - t / 4) * ε * n := mul_le_mul_of_nonneg_right hε' hn0
    have h6 : t / 2 * k ≤ t / 2 * n := mul_le_mul_of_nonneg_left hUN (by linarith)
    have h1 : x * (n * t / 4) ≤ x * ((1 - t / 4) * ε * n - t / 2 * k) := by
      apply mul_le_mul_of_nonneg_left _ hx0
      linarith
    have h7 : x * ((1 - t / 4) * ε * n - t / 2 * k)
        = x * (1 - t / 4) * (k + ε * n) - k * (1 + t / 4) * x := by ring
    linarith
  have hm0 : 0 ≤ m := hMr.le
  have key4 : x * (n * t / 4) ≤ t ^ 2 / 48 * n * m := by
    have : b * m ≤ t ^ 2 / 48 * n * m := mul_le_mul_of_nonneg_right hb hm0
    linarith
  have hnt : 0 < n * t / 4 := by positivity
  have hx12 : x ≤ t / 12 * m := by
    have e5 : t ^ 2 / 48 * n * m = (t / 12 * m) * (n * t / 4) := by ring
    rw [e5] at key4
    exact le_of_mul_le_mul_right key4 hnt
  have : t / 12 * m < t / 3 * m := by
    have : 0 < t * m := by positivity
    linarith
  have hcon' : t / 3 * m < x := hcon
  linarith


lemma nbrV_random {Ω : Type*} (M : ℕ → ℕ) (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool)
    (ω : Ω) (N : ℕ) (v : Fin N) :
    nbrV M (randomGraph M adj ω) N v = Finset.univ.filter (fun w => adj N ω v w = true) := by
  ext w; simp [nbrV, randomGraph, edgeSetOf]

lemma ae_regular {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M c : ℕ → ℕ) (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool)
    (hadj : IsRandomServerRegular P M c adj) :
    ∀ᵐ ω ∂P, ∀ N, ∀ v : Fin N, (nbrV M (randomGraph M adj ω) N v).card = c N := by
  classical
  rw [ae_all_iff]
  intro N
  rw [ae_iff]
  have hsub : {ω | ¬ ∀ v : Fin N, (nbrV M (randomGraph M adj ω) N v).card = c N}
      ⊆ ⋃ a ∈ {a : Fin N → Fin (M N) → Bool | ¬ IsServerRegular (c N) a}, adj N ⁻¹' {a} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    refine ⟨adj N ω, ?_, rfl⟩
    intro hreg
    apply hω
    intro v
    rw [nbrV_random]
    exact hreg v
  apply measure_mono_null hsub
  rw [measure_biUnion_null_iff (Set.to_countable _)]
  intro a ha
  rw [(hadj N).2 a, if_neg ha]

end StrictCompatLB.RegularDegree.A4aux

open StrictCompatLB.RegularDegree StrictCompatLB.MeanField StrictCompatLB.RegularDegree.A4aux in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M c : ℕ → ℕ) (hc_pos : ∀ N, 1 ≤ c N) (hcM : ∀ N, c N ≤ M N)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) (hadj : IsRandomServerRegular P M c adj)
    (hc : Tendsto (fun N : ℕ => (c N : ℝ)) atTop atTop)
    (hNcM : Tendsto (fun N : ℕ => (N : ℝ) * (c N : ℝ) / (M N : ℝ)) atTop atTop) :
    ∀ᵐ ω ∂P, StrictCompatLB.MeanField.IsPropSparse M (randomGraph M adj ω) := by
  classical
  have hA2 : ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ X : Finset (Fin (M N)),
      (1 / ((k:ℝ) + 1)) / 3 * (M N : ℝ) ≤ (X.card : ℝ) →
        ((badServers M c (randomGraph M adj ω) ((1 / ((k:ℝ) + 1)) / 4) N X).card : ℝ)
          ≤ (1 / ((k:ℝ) + 1)) ^ 2 / 48 * (N : ℝ) := by
    rw [ae_all_iff]
    intro k
    have ht : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
    have ht1 : 1 / ((k:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    exact lemma_A_2 P M c hc_pos hcM adj hadj hc hNcM _ (by positivity) (by linarith) _
      (by positivity) (by nlinarith) _ (by positivity)
  have hA3 : ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀,
      ((lowDegreeDispatchers M c (randomGraph M adj ω) ((1 / ((k:ℝ) + 1)) / 4) N).card : ℝ)
        ≤ (1 / ((k:ℝ) + 1)) / 3 * (M N : ℝ) := by
    rw [ae_all_iff]
    intro k
    exact lemma_A_3 P M c hc_pos hcM adj hadj hc hNcM _ (by positivity) _ (by positivity)
  filter_upwards [hA2, hA3, ae_regular P M c adj hadj] with ω h2 h3 hreg
  intro ε hε δ hδ
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (lt_min hε hδ)
  set t : ℝ := 1 / ((k:ℝ) + 1) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have htε : t ≤ ε := (hk.trans_le (min_le_left _ _)).le
  have htδ : t ≤ δ := (hk.trans_le (min_le_right _ _)).le
  obtain ⟨N₁, hN₁, hN₁'⟩ := h2 k
  obtain ⟨N₂, -, hN₂'⟩ := h3 k
  refine ⟨max N₁ N₂, fun N hN U => ?_⟩
  have hN1 : N ≥ N₁ := le_trans (le_max_left _ _) hN
  have hN2 : N ≥ N₂ := le_trans (le_max_right _ _) hN
  set G := randomGraph M adj ω
  have hNpos : 0 < N := by omega
  have hcpos : 0 < c N := by have := hc_pos N; omega
  have hMpos : 0 < M N := by have := hc_pos N; have := hcM N; omega
  have hNr : (0:ℝ) < N := by exact_mod_cast hNpos
  have hMr : (0:ℝ) < M N := by exact_mod_cast hMpos
  have hcr : (0:ℝ) < c N := by exact_mod_cast hcpos
  set A := lowDegreeDispatchers M c G (t / 4) N
  set X1 := Finset.univ.filter (fun w : Fin (M N) => w ∉ A ∧
    ((nbrW M G N w).card : ℝ) * ((U.card : ℝ) / N + ε) ≤ ((nbrW M G N w ∩ U).card : ℝ))
  set X2 := Finset.univ.filter (fun w : Fin (M N) => w ∉ A ∧
    ((nbrW M G N w).card : ℝ) * ((Uᶜ.card : ℝ) / N + ε) ≤ ((nbrW M G N w ∩ Uᶜ).card : ℝ))
  have hX1 : (X1.card : ℝ) ≤ t / 3 * M N :=
    over_bound M c G N hNpos hcpos hMpos (hreg N) ε t ht0 htε ht1 (hN₁' N hN1) U X1
      (fun w hw => (Finset.mem_filter.mp hw).2.1) (fun w hw => (Finset.mem_filter.mp hw).2.2)
  have hX2 : (X2.card : ℝ) ≤ t / 3 * M N :=
    over_bound M c G N hNpos hcpos hMpos (hreg N) ε t ht0 htε ht1 (hN₁' N hN1) Uᶜ X2
      (fun w hw => (Finset.mem_filter.mp hw).2.1) (fun w hw => (Finset.mem_filter.mp hw).2.2)
  have hAc : (A.card : ℝ) ≤ t / 3 * M N := hN₂' N hN2
  have hsub : Finset.univ.filter (fun w : Fin (M N) =>
        ε ≤ |((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - (U.card : ℝ) / (N : ℝ)|) ⊆ A ∪ (X1 ∪ X2) := by
    intro w hw
    have hw' := (Finset.mem_filter.mp hw).2
    by_cases hwA : w ∈ A
    · exact Finset.mem_union_left _ hwA
    apply Finset.mem_union_right
    have hdeg : (1 - t / 4) * ((N : ℝ) * c N / M N) < ((nbrW M G N w).card : ℝ) := by
      simpa [A, lowDegreeDispatchers] using hwA
    have hμ : 0 < (1 - t / 4) * ((N : ℝ) * c N / M N) := by
      have : 0 < 1 - t / 4 := by linarith
      positivity
    have hnw : 0 < ((nbrW M G N w).card : ℝ) := lt_trans hμ hdeg
    have hsd : ((nbrW M G N w ∩ Uᶜ).card : ℝ)
        = ((nbrW M G N w).card : ℝ) - ((nbrW M G N w ∩ U).card : ℝ) := by
      have h := Finset.card_sdiff_add_card_inter (nbrW M G N w) U
      rw [← Finset.sdiff_eq_inter_compl]
      have : ((nbrW M G N w \ U).card : ℝ) + ((nbrW M G N w ∩ U).card : ℝ)
          = ((nbrW M G N w).card : ℝ) := by exact_mod_cast h
      linarith
    set nw : ℝ := ((nbrW M G N w).card : ℝ)
    set aw : ℝ := ((nbrW M G N w ∩ U).card : ℝ)
    have hUc : ((Uᶜ.card : ℕ) : ℝ) = N - U.card := by
      rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub (by simpa using Finset.card_le_univ U)]
    rcases le_abs'.mp hw' with h | h
    · -- u - r ≥ ε
      apply Finset.mem_union_right
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwA, ?_⟩
      rw [hsd, hUc]
      have h' : aw / nw ≤ (U.card : ℝ) / N - ε := by linarith
      rw [div_le_iff₀ hnw] at h'
      have : ((N : ℝ) - U.card) / N = 1 - (U.card : ℝ) / N := by field_simp
      rw [this]
      nlinarith
    · apply Finset.mem_union_left
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwA, ?_⟩
      have h' : (U.card : ℝ) / N + ε ≤ aw / nw := by linarith
      rw [le_div_iff₀ hnw] at h'
      linarith
  calc ((Finset.univ.filter (fun w : Fin (M N) =>
        ε ≤ |((nbrW M G N w ∩ U).card : ℝ) / ((nbrW M G N w).card : ℝ)
              - (U.card : ℝ) / (N : ℝ)|)).card : ℝ)
      ≤ ((A ∪ (X1 ∪ X2)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (A.card : ℝ) + (X1.card + X2.card) := by
        have h1 := Finset.card_union_le A (X1 ∪ X2)
        have h2 := Finset.card_union_le X1 X2
        have : (A ∪ (X1 ∪ X2)).card ≤ A.card + (X1.card + X2.card) := by omega
        exact_mod_cast this
    _ ≤ t * M N := by linarith
    _ ≤ δ * M N := by exact mul_le_mul_of_nonneg_right htδ hMr.le
