-- Prove2me | solution 1 for SmithRenewal.Elementary.truncation_comparison
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T02:43:31.544428+00:00
-- url     : https://prove2.me/submissions/3f2db0ce-5f02-4cd8-81e5-0ed122e49b51

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open SmithRenewal.Elementary

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    IsRenewalProcess P (trunc Δ X) ∧
    (∀ n ω, S (trunc Δ X) n ω ≤ S X n ω) ∧
    (∀ t ω, N X t ω ≤ N (trunc Δ X) t ω) ∧
    (∀ t, H X P t ≤ H (trunc Δ X) P t) ∧
    (∀ t, 0 ≤ t → ∀ ω, zeta (trunc Δ X) t ω ≤ Δ) := by
  classical
  have hm : Measurable (fun v : ℝ => min v Δ) := measurable_id.min measurable_const
  have ht : IsRenewalProcess P (trunc Δ X) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact (hX.measurable i).min measurable_const
    · exact hX.indep.comp (fun _ => fun v : ℝ => min v Δ) (fun _ => hm)
    · intro i
      exact (hX.identDistrib i).comp hm
    · intro i ω
      exact le_min (hX.nonneg i ω) hΔ.le
    · have he : {ω | trunc Δ X 0 ω = 0} = {ω | X 0 ω = 0} := by
        ext ω
        simp only [trunc, Set.mem_setOf_eq]
        constructor
        · intro h
          rcases min_cases (X 0 ω) Δ with h' | h'
          · exact h'.1.symm.trans h
          · exact False.elim (ne_of_gt hΔ (h'.1.symm.trans h))
        · intro h
          simp [h, hΔ.le]
      rw [he]
      exact hX.not_ae_zero
  have hsum : ∀ n ω, S (trunc Δ X) n ω ≤ S X n ω := by
    intro n ω
    exact Finset.sum_le_sum (fun i _ => min_le_left (X i ω) Δ)
  have hcount : ∀ t ω, N X t ω ≤ N (trunc Δ X) t ω := by
    intro t ω
    exact Set.encard_mono (fun n hn => ⟨hn.1, (hsum n ω).trans hn.2⟩)
  refine ⟨ht, hsum, hcount, ?_, ?_⟩
  · intro t
    exact lintegral_mono (fun ω => ENat.toENNReal_mono (hcount t ω))
  · intro t ht0 ω
    have hstep (k : ℕ) : S (trunc Δ X) (k + 1) ω =
        S (trunc Δ X) k ω + min (X k ω) Δ := by
      simp [S, Finset.sum_range_succ, trunc]
    have hmono : Monotone (fun k => S (trunc Δ X) k ω) := by
      apply monotone_nat_of_le_succ
      intro k
      rw [hstep]
      exact le_add_of_nonneg_right (ht.nonneg k ω)
    unfold zeta
    by_cases hn : N (trunc Δ X) t ω = ⊤
    · simp only [hn, ENat.toNat_top, zero_add]
      rw [hstep]
      simp only [S, Finset.range_zero, Finset.sum_empty, zero_add]
      linarith [min_le_right (X 0 ω) Δ]
    · let k := (N (trunc Δ X) t ω).toNat
      have hk : (k : ℕ∞) = N (trunc Δ X) t ω := ENat.coe_toNat hn
      have hkt : S (trunc Δ X) k ω ≤ t := by
        by_cases hk0 : k = 0
        · simpa [hk0, S] using ht0
        · by_contra hb
          have hsub : {j : ℕ | 1 ≤ j ∧ S (trunc Δ X) j ω ≤ t} ⊆
              (↑(Finset.Ico 1 k) : Set ℕ) := by
            intro j hj
            simp only [Finset.mem_coe, Finset.mem_Ico]
            refine ⟨hj.1, ?_⟩
            by_contra hjk
            have := hmono (Nat.le_of_not_gt hjk)
            have hjt : S (trunc Δ X) j ω ≤ t := hj.2
            linarith
          have hc := Set.encard_mono hsub
          rw [Set.encard_coe_eq_coe_finsetCard, Nat.card_Ico] at hc
          change N (trunc Δ X) t ω ≤ ((k - 1 : ℕ) : ℕ∞) at hc
          rw [← hk] at hc
          have hc' : k ≤ k - 1 := by exact_mod_cast hc
          omega
      change S (trunc Δ X) (k + 1) ω - t ≤ Δ
      rw [hstep]
      linarith [min_le_right (X k ω) Δ]

#print axioms solution
