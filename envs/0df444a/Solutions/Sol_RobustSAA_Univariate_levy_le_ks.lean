-- Prove2me | solution 1 for RobustSAA.Univariate.levy_le_ks
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:03:48.177317+00:00
-- url     : https://prove2.me/submissions/dc62499a-8a67-461e-9bc1-cb23d0c50397

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

open Filter MeasureTheory RobustSAA.Univariate

namespace RSAA3LK

lemma card_ord_eq {N : ℕ} (s : Fin N → ℝ) (t : ℝ) :
    (Finset.univ.filter (fun i => ord s i ≤ t)).card =
      (Finset.univ.filter (fun i => s i ≤ t)).card := by
  refine Finset.card_equiv (Tuple.sort s) (fun i => ?_)
  rw [Finset.mem_filter, Finset.mem_filter]
  simp [ord]

lemma ord_mono {N : ℕ} (s : Fin N → ℝ) : Monotone (ord s) := Tuple.monotone_sort s

lemma cdf_mono (F₀ : ProbabilityMeasure ℝ) : Monotone (cdfOf F₀) :=
  ProbabilityTheory.monotone_cdf _

lemma empCdf_mono {N : ℕ} (s : Fin N → ℝ) : Monotone (empCdf s) := by
  intro a b hab
  unfold empCdf
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact le_trans hi hab)

/-- Let `k = #{j : s j ≤ t}`. If `k ≥ 1` then the `k`-th order statistic is `≤ t`. -/
lemma ord_le_of_lt_card {N : ℕ} (s : Fin N → ℝ) (t : ℝ) (i : Fin N)
    (hi : (i : ℕ) < (Finset.univ.filter (fun j => s j ≤ t)).card) : ord s i ≤ t := by
  by_contra h
  push Not at h
  have hsub : Finset.univ.filter (fun j => ord s j ≤ t) ⊆
      Finset.univ.filter (fun j : Fin N => (j : ℕ) < i) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_contra hji
    push Not at hji
    have := ord_mono s (show i ≤ j from hji)
    linarith
  have h1 := Finset.card_le_card hsub
  rw [card_ord_eq, Fin.card_filter_val_lt] at h1
  have : min N (i : ℕ) ≤ i := min_le_right _ _
  omega

lemma lt_ord_of_card_le {N : ℕ} (s : Fin N → ℝ) (t : ℝ) (i : Fin N)
    (hi : (Finset.univ.filter (fun j => s j ≤ t)).card ≤ (i : ℕ)) : t < ord s i := by
  by_contra h
  push Not at h
  have hsub : Finset.univ.filter (fun j : Fin N => (j : ℕ) < (i : ℕ) + 1) ⊆
      Finset.univ.filter (fun j => ord s j ≤ t) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact le_trans (ord_mono s (show j ≤ i from Nat.lt_succ_iff.mp hj)) h
  have h1 := Finset.card_le_card hsub
  rw [card_ord_eq, Fin.card_filter_val_lt] at h1
  have := i.isLt
  omega

lemma term_le_ks {N : ℕ} (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) (i : Fin N) :
    max (((i : ℕ) + 1 : ℝ) / N - u F₀ s i) (u F₀ s i - ((i : ℕ) : ℝ) / N) ≤ ksStat F₀ s := by
  unfold ksStat
  exact le_ciSup (f := fun i : Fin N =>
    max (((i : ℕ) + 1 : ℝ) / N - u F₀ s i) (u F₀ s i - ((i : ℕ) : ℝ) / N))
    (Set.finite_range _).bddAbove i

lemma emp_sub_le {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) (t : ℝ) :
    empCdf s t - cdfOf F₀ t ≤ ksStat F₀ s ∧ cdfOf F₀ t - empCdf s t ≤ ksStat F₀ s := by
  set k := (Finset.univ.filter (fun j => s j ≤ t)).card with hk
  have hkN : k ≤ N := by
    have := Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun j => s j ≤ t)
    simpa [hk] using this
  have hemp : empCdf s t = (k : ℝ) / N := rfl
  have hc0 : 0 ≤ cdfOf F₀ t := ProbabilityTheory.cdf_nonneg _ _
  have hc1 : cdfOf F₀ t ≤ 1 := ProbabilityTheory.cdf_le_one _ _
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [hemp, h0]
      have h := term_le_ks F₀ s ⟨0, hN⟩
      have hu : 0 ≤ u F₀ s ⟨0, hN⟩ := ProbabilityTheory.cdf_nonneg _ _
      simp only [Nat.cast_zero, zero_div] at h ⊢
      have := le_trans (le_max_right _ _) h
      linarith
    · have hi : k - 1 < N := by omega
      have hle := ord_le_of_lt_card s t ⟨k - 1, hi⟩ (by simp; omega)
      have hu : u F₀ s ⟨k - 1, hi⟩ ≤ cdfOf F₀ t := cdf_mono F₀ hle
      have h := le_trans (le_max_left _ _) (term_le_ks F₀ s ⟨k - 1, hi⟩)
      have hcast : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by
        rw [Nat.cast_sub (by omega)]; simp
      simp only [hcast] at h
      rw [hemp]; linarith
  · rcases lt_or_eq_of_le hkN with hlt | heq
    · have hlt' := lt_ord_of_card_le s t ⟨k, hlt⟩ le_rfl
      have hu : cdfOf F₀ t ≤ u F₀ s ⟨k, hlt⟩ := cdf_mono F₀ hlt'.le
      have h := le_trans (le_max_right _ _) (term_le_ks F₀ s ⟨k, hlt⟩)
      simp only at h
      rw [hemp]; linarith
    · rw [hemp, heq, div_self hNr.ne']
      have hi : N - 1 < N := by omega
      have h := le_trans (le_max_left _ _) (term_le_ks F₀ s ⟨N - 1, hi⟩)
      have hu : u F₀ s ⟨N - 1, hi⟩ ≤ 1 := ProbabilityTheory.cdf_le_one _ _
      have hcast : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
        rw [Nat.cast_sub (by omega)]; simp
      simp only [hcast, div_self hNr.ne'] at h
      linarith

end RSAA3LK

open RSAA3LK

theorem solution {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) :
    levyDist (empCdf s) (cdfOf F₀) ≤ ksStat F₀ s := by
  have hD0 : 0 ≤ ksStat F₀ s := by
    have h := emp_sub_le hN F₀ s 0
    linarith [h.1, h.2]
  refine le_of_forall_pos_le_add (fun δ hδ => ?_)
  apply csInf_le ⟨0, fun _ h => le_of_lt h.1⟩
  refine ⟨by linarith, fun ξ => ⟨?_, ?_⟩⟩
  · have h1 := (emp_sub_le hN F₀ s (ξ - (ksStat F₀ s + δ))).1
    have h2 := cdf_mono F₀ (show ξ - (ksStat F₀ s + δ) ≤ ξ by linarith)
    linarith
  · have h1 := (emp_sub_le hN F₀ s ξ).2
    have h2 := empCdf_mono s (show ξ ≤ ξ + (ksStat F₀ s + δ) by linarith)
    linarith
