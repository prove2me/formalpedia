-- Prove2me | solution 1 for SolarTariff.Fair.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:18:09.950459+00:00
-- url     : https://prove2.me/submissions/b6c6e76c-45c6-4f91-9e9a-69a5ec3875d2

import Mathlib
import Definitions.Def_SolarTariff_Fair_Model

namespace SolarTariff.Fair

lemma p5_ite_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) (a b : ι → ℝ) :
    ∑ i, (if i ∈ A then a i else b i) = ∑ i, b i + ∑ i ∈ A, (a i - b i) := by
  have : ∀ i, (if i ∈ A then a i else b i) = b i + (if i ∈ A then a i - b i else 0) := by
    intro i; split_ifs <;> ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]

lemma p5_sum_outflow {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Market ι) (B : Bills ι)
    (A : Finset ι) (ps : ℝ) :
    ∑ i, M.h i * outflowChange M B A ps i =
      utilityChange M B A + M.cuStar * EOf M A + (M.pr0 - M.cu0) * E0 M
        + ps * DeltaE M A - M.pr0 * E0 M := by
  have h1 : ∀ i, M.h i * outflowChange M B A ps i =
      (if i ∈ A then M.h i * B.adopt i + ps * (M.h i * M.g i) else M.h i * B.nonAdopt i)
        - M.pr0 * (M.h i * M.d i) := by
    intro i; unfold outflowChange; split_ifs <;> ring
  have h2 : ∀ i, M.h i * (if i ∈ A then B.adopt i else B.nonAdopt i) =
      (if i ∈ A then M.h i * B.adopt i else M.h i * B.nonAdopt i) := by
    intro i; split_ifs <;> ring
  simp_rw [h1]
  unfold utilityChange E0 DeltaE
  simp_rw [h2]
  rw [Finset.sum_sub_distrib, p5_ite_sum, p5_ite_sum, ← Finset.mul_sum, Finset.mul_sum]
  have : ∑ i ∈ A, (M.h i * B.adopt i + ps * (M.h i * M.g i) - M.h i * B.nonAdopt i)
      = ∑ i ∈ A, (M.h i * B.adopt i - M.h i * B.nonAdopt i) + ∑ i ∈ A, ps * (M.h i * M.g i) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl ?_; intro i _; ring
  rw [this, Finset.mul_sum]
  have e : ∀ x, M.pr0 * (M.h x * M.d x) = M.pr0 * M.h x * M.d x := fun x => by ring
  have e2 : ∀ x, ps * (M.h x * M.g x) = ps * M.h x * M.g x := fun x => by ring
  simp only [e, e2]
  rw [Finset.mul_sum (s := A)]
  simp only [← mul_assoc]; ring

lemma p5_diff {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Market ι) (τ : T3 ι) (i : ι) :
    (τ.bills M).nonAdopt i - (τ.bills M).adopt i = τ.pr * M.g i - τ.f i := by
  simp only [T3.bills, gridUsage]; ring

lemma p5_thr {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Market ι) (hM : M.Standing)
    (A : Finset ι) (i : ι) : threshold M ((TStar M A).bills M) i = tStar M A i := by
  have hg := hM.2.2.1 i
  unfold threshold; rw [p5_diff]; simp only [TStar]; field_simp; ring

lemma p5_DE_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Market ι) (hM : M.Standing)
    (A : Finset ι) (hA : A.Nonempty) : 0 < DeltaE M A :=
  Finset.sum_pos (fun i _ => mul_pos (hM.1 i) (hM.2.2.1 i)) hA

lemma p5_DE_mono {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Market ι) (hM : M.Standing)
    (A : Finset ι) : DeltaE M A ≤ DeltaE M Finset.univ :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => (mul_pos (hM.1 i) (hM.2.2.1 i)).le)

lemma p5_E0_pos {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : Market ι)
    (hM : M.Standing) : 0 < E0 M :=
  Finset.sum_pos (fun i _ => mul_pos (hM.1 i) (hM.2.1 i)) Finset.univ_nonempty

end SolarTariff.Fair

open SolarTariff.Fair

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Market ι) (hM : M.Standing) (A : Finset ι)
    (hA : Admissible M A) :
    let B := (TStar M A).bills M
    FeasibleP2 M A B (tm M A) ∧
    (0 ≤ dC M A → objective M B A (tm M A) ≤ 0) ∧
    (0 ≤ dC M A → (∃ k, k ∉ A ∧ ∀ i, M.d k ≤ M.d i) →
      ∀ (τ : T3 ι) (ps : ℝ), FeasibleP2 M A (τ.bills M) ps →
        objective M B A (tm M A) ≤ objective M (τ.bills M) A ps) := by
  intro B
  have hDA := p5_DE_pos M hM A hA.1
  have hDU := p5_DE_mono M hM A
  have hE0 := p5_E0_pos M hM
  have hcs : M.cs (DeltaE M Finset.univ) ≤ M.cs (DeltaE M A) := hM.2.2.2.2.1 hDU
  have hdS := hM.2.2.2.2.2
  have htm : tm M A * DeltaE M A = M.cs (DeltaE M A) * DeltaE M A + M.dS := by
    unfold tm; field_simp
  have htm_gt : M.cs (DeltaE M A) < tm M A := by
    unfold tm; have := div_pos hdS hDA; linarith
  have hthr : ∀ i, threshold M B i = tStar M A i := p5_thr M hM A
  -- adopters of T* at any price
  have hadA : ∀ p, M.cs (DeltaE M Finset.univ) < p → p ≤ tm M A → adopters M B p = A := by
    intro p h1 h2; ext i
    simp only [adopters, Finset.mem_filter, Finset.mem_univ, true_and, hthr, tStar]
    split_ifs with hi
    · simp [hi, h2]
    · simp [hi]; linarith
  have hadE : ∀ p, tm M A < p → adopters M B p = ∅ := by
    intro p h1; ext i
    simp only [adopters, Finset.mem_filter, Finset.mem_univ, true_and, hthr, tStar,
      Finset.notMem_empty, iff_false]
    split_ifs <;> linarith
  have hadU : ∀ p, p ≤ M.cs (DeltaE M Finset.univ) → adopters M B p = Finset.univ := by
    intro p h1; ext i
    simp only [adopters, Finset.mem_filter, Finset.mem_univ, true_and, hthr, tStar, iff_true]
    split_ifs <;> linarith
  have hadtm : adopters M B (tm M A) = A := hadA _ (by linarith) le_rfl
  have hUtil : utilityChange M B A = M.dU := by
    have hsum : ∑ i, M.h i * (if i ∈ A then B.adopt i else B.nonAdopt i)
        = prStar M A * E0 M - ∑ i ∈ A, M.h i * M.g i * tStar M A i := by
      have : ∀ i, M.h i * (if i ∈ A then B.adopt i else B.nonAdopt i) =
          (if i ∈ A then M.h i * B.adopt i else M.h i * B.nonAdopt i) := by
        intro i; split_ifs <;> ring
      simp_rw [this]; rw [p5_ite_sum]
      simp only [B, TStar, T3.bills, gridUsage, E0]
      rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · refine Finset.sum_congr rfl ?_; intro i _; ring
      · refine Finset.sum_congr rfl ?_; intro i _; ring
    unfold utilityChange; rw [hsum]
    unfold prStar; rw [div_mul_cancel₀ _ hE0.ne']; ring
  have hsumT : ∀ (B' : Bills ι) (ps : ℝ), utilityChange M B' A = M.dU →
      ps * DeltaE M A = M.cs (DeltaE M A) * DeltaE M A + M.dS →
      ∑ i, M.h i * outflowChange M B' A ps i = - dC M A := by
    intro B' ps hu hp
    rw [p5_sum_outflow, hu, hp]; unfold dC dWF EOf; ring
  -- T*'s outflow is (pr* - pr0) d_i
  have houtT : ∀ i, outflowChange M B A (tm M A) i = (prStar M A - M.pr0) * M.d i := by
    intro i
    simp only [outflowChange, B, TStar, T3.bills, gridUsage]
    split_ifs with hi
    · simp only [tStar, hi, if_true]; ring
    · ring
  have hpr : (prStar M A - M.pr0) * E0 M = - dC M A := by
    rw [← hsumT B (tm M A) hUtil htm]; unfold E0
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl ?_; intro i _; rw [houtT]; ring
  refine ⟨⟨hadtm, ?_, ?_, hUtil⟩, ?_, ?_⟩
  · unfold solarProfit; rw [hadtm]; linarith
  · intro p hp
    rcases lt_or_gt_of_ne hp with hlt | hgt
    · by_cases hc : p ≤ M.cs (DeltaE M Finset.univ)
      · unfold solarProfit; rw [hadU p hc]
        have : (p - M.cs (DeltaE M Finset.univ)) * DeltaE M Finset.univ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        linarith
      · push Not at hc
        unfold solarProfit; rw [hadA p hc hlt.le]
        nlinarith
    · unfold solarProfit; rw [hadE p hgt]; simp [DeltaE]; exact hdS
  · intro hC
    have hneg : prStar M A - M.pr0 ≤ 0 := by
      by_contra h; push Not at h; nlinarith
    unfold objective
    apply Finset.sup'_le; intro i _
    rw [houtT]; exact mul_nonpos_of_nonpos_of_nonneg hneg (hM.2.1 i).le
  · intro hC ⟨k, hk, hkmin⟩ τ ps hF
    obtain ⟨hadτ, hsp, _, huτ⟩ := hF
    have hneg : prStar M A - M.pr0 ≤ 0 := by
      by_contra h; push Not at h; nlinarith
    have hps : ps * DeltaE M A = M.cs (DeltaE M A) * DeltaE M A + M.dS := by
      unfold solarProfit at hsp; rw [hadτ] at hsp; linarith
    have hsτ := hsumT (τ.bills M) ps huτ hps
    -- each outflow of τ is at most (pr_τ - pr0) d_i
    have hle : ∀ i, outflowChange M (τ.bills M) A ps i ≤ (τ.pr - M.pr0) * M.d i := by
      intro i
      have hd := p5_diff M τ i
      by_cases hi : i ∈ A
      · have hth : ps ≤ threshold M (τ.bills M) i := by
          have : i ∈ adopters M (τ.bills M) ps := by rw [hadτ]; exact hi
          simpa [adopters] using this
        unfold threshold at hth; rw [hd, le_div_iff₀ (hM.2.2.1 i)] at hth
        simp only [outflowChange, hi, if_true]
        simp only [T3.bills, gridUsage] at hd ⊢
        nlinarith
      · simp only [outflowChange, hi, if_false, T3.bills]; ring_nf; rfl
    have hprle : prStar M A ≤ τ.pr := by
      have : - dC M A ≤ (τ.pr - M.pr0) * E0 M := by
        rw [← hsτ]; unfold E0; rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro i _
        have := hle i
        have hh := hM.1 i
        nlinarith
      nlinarith
    have hk_out : outflowChange M (τ.bills M) A ps k = (τ.pr - M.pr0) * M.d k := by
      simp only [outflowChange, hk, if_false, T3.bills]; ring
    calc objective M B A (tm M A) ≤ (prStar M A - M.pr0) * M.d k := by
          unfold objective; apply Finset.sup'_le; intro i _
          rw [houtT]; exact mul_le_mul_of_nonpos_left (hkmin i) hneg
      _ ≤ (τ.pr - M.pr0) * M.d k :=
          mul_le_mul_of_nonneg_right (by linarith) (hM.2.1 k).le
      _ = outflowChange M (τ.bills M) A ps k := hk_out.symm
      _ ≤ objective M (τ.bills M) A ps := by
          unfold objective; exact Finset.le_sup' _ (Finset.mem_univ k)
