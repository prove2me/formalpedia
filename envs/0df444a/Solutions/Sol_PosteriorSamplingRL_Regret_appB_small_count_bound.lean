-- Prove2me | solution 1 for PosteriorSamplingRL.Regret.appB_small_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:33:53.892394+00:00
-- url     : https://prove2.me/submissions/568fd1c4-4339-43fc-b546-db424154eb78

import Mathlib
import Definitions.Def_PosteriorSamplingRL_Regret_Confidence
set_option autoImplicit false
open PosteriorSamplingRL.Regret

lemma psr_seq_bound (τ : ℕ) (n : ℕ → ℕ) (hn : ∀ k, n k ≤ τ) (m : ℕ) :
    (∑ k ∈ Finset.range m, if ∑ l ∈ Finset.range k, n l ≤ τ then n k else 0) ≤ 2 * τ ∧
    ((∑ l ∈ Finset.range m, n l ≤ τ) →
      (∑ k ∈ Finset.range m, if ∑ l ∈ Finset.range k, n l ≤ τ then n k else 0) =
        ∑ l ∈ Finset.range m, n l) := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hnm := hn m
    by_cases hN : ∑ l ∈ Finset.range m, n l ≤ τ
    · have e := ih2 hN
      simp only [hN, if_true]
      rw [e]
      refine ⟨by omega, fun _ => rfl⟩
    · simp only [hN, if_false, add_zero]
      refine ⟨ih1, fun h => ?_⟩
      exfalso; apply hN; omega

lemma psr_visit_eq_sum {S A τ : ℕ} (sa : ℕ → Fin τ → Fin S × Fin A) (k : ℕ) (p : Fin S × Fin A) :
    visitCount sa k p = ∑ l ∈ Finset.range k, (Finset.univ.filter (fun j : Fin τ => sa l j = p)).card := by
  unfold visitCount
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.card_filter]

theorem solution (S A τ : ℕ) (sa : ℕ → Fin τ → Fin S × Fin A) (m : ℕ) :
    ∑ k ∈ Finset.range m, ∑ j : Fin τ,
        (if visitCount sa k (sa k j) ≤ τ then (1 : ℝ) else 0)
      ≤ 2 * (τ : ℝ) * S * A := by
  classical
  set nn : Fin S × Fin A → ℕ → ℕ := fun p k => (Finset.univ.filter (fun j : Fin τ => sa k j = p)).card with hnn
  have hnn_le : ∀ p k, nn p k ≤ τ := by
    intro p k
    calc nn p k ≤ (Finset.univ : Finset (Fin τ)).card := Finset.card_filter_le _ _
      _ = τ := by simp
  have hvis : ∀ k p, visitCount sa k p = ∑ l ∈ Finset.range k, nn p l := fun k p => psr_visit_eq_sum sa k p
  -- regroup by the visited pair
  have hgroup : ∑ k ∈ Finset.range m, ∑ j : Fin τ,
        (if visitCount sa k (sa k j) ≤ τ then (1 : ℝ) else 0) =
      ∑ p : Fin S × Fin A, ((∑ k ∈ Finset.range m,
        if ∑ l ∈ Finset.range k, nn p l ≤ τ then nn p k else 0 : ℕ) : ℝ) := by
    have h1 : ∀ k j, (if visitCount sa k (sa k j) ≤ τ then (1 : ℝ) else 0) =
        ∑ p : Fin S × Fin A, if sa k j = p then
          (if ∑ l ∈ Finset.range k, nn p l ≤ τ then (1 : ℝ) else 0) else 0 := by
      intro k j
      rw [Finset.sum_ite_eq]
      simp [hvis]
    simp_rw [h1]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases h : ∑ l ∈ Finset.range k, nn p l ≤ τ <;> simp [h, hnn]
  rw [hgroup]
  calc _ ≤ ∑ _p : Fin S × Fin A, ((2 * τ : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        exact_mod_cast (psr_seq_bound τ (nn p) (hnn_le p) m).1
    _ = 2 * (τ : ℝ) * S * A := by simp; ring
