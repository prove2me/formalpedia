-- Prove2me | solution 1 for QueueBandit.EarlyLower.theorem_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:57:01.2748+00:00
-- url     : https://prove2.me/submissions/9101952e-9ca9-4b6d-b62f-35b1d2871267
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QueueBandit_EarlyLower_Model
import Definitions.Def_QueueBandit_LateLower_Dynamics
import Theorems.Thm_QueueBandit_EarlyLower_corollary_20
import Theorems.Thm_QueueBandit_EarlyLower_lemma_22

open QueueBandit.LateLower QueueBandit.EarlyLower

/-- For `a > 0`, once `log t` is large, `2 (a log t − c) − log t / log log t ≥ 6`. -/
lemma qb8_eventually (a c : ℝ) (ha : 0 < a) : ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, B ≤ Real.log t →
    6 ≤ 2 * (a * Real.log t - c) - Real.log t / Real.log (Real.log t) := by
  refine ⟨max (Real.exp (2 / a)) ((6 + 2 * |c|) * 2 / (3 * a)),
    lt_max_of_lt_left (Real.exp_pos _), ?_⟩
  intro t ht
  have h1 : Real.exp (2 / a) ≤ Real.log t := le_trans (le_max_left _ _) ht
  have h2 : (6 + 2 * |c|) * 2 / (3 * a) ≤ Real.log t := le_trans (le_max_right _ _) ht
  have hlpos : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos _) h1
  have hll : 2 / a ≤ Real.log (Real.log t) := (Real.le_log_iff_exp_le hlpos).2 h1
  have hR : Real.log t / Real.log (Real.log t) ≤ Real.log t / (2 / a) :=
    div_le_div_of_nonneg_left hlpos.le (by positivity) hll
  have he : Real.log t / (2 / a) = a * Real.log t / 2 := by field_simp
  have h3 : (6 + 2 * |c|) * 2 ≤ Real.log t * (3 * a) := by
    rwa [div_le_iff₀ (by positivity)] at h2
  have hc : c ≤ |c| := le_abs_self c
  rw [he] at hR
  nlinarith

lemma qb8_gapMin_nonneg {U K : ℕ} (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hA1 : Assumption1 mu kstar) : 0 ≤ gapMin mu kstar := by
  unfold gapMin
  split_ifs with h
  · rw [Finset.le_inf'_iff]
    intro p hp
    have hp' : p.2 ≠ kstar p.1 := (Finset.mem_filter.1 hp).2
    have := hA1.2 p.1 p.2 hp'
    unfold gap; linarith
  · exact le_rfl

lemma qb8_gapMin_le {U K : ℕ} (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (u : Fin U) (k : Fin K) (hk : k ≠ kstar u) : gapMin mu kstar ≤ gap mu kstar u k := by
  have hmem : (u, k) ∈ subPairs kstar := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
  unfold gapMin
  rw [dif_pos ⟨_, hmem⟩]
  exact Finset.inf'_le (fun p => gap mu kstar p.1 p.2) hmem

lemma qb8_expCount_nonneg {U K : ℕ} (π : Policy U K) (mu : Fin U → Fin K → ℝ) (u : Fin U)
    (k : Fin K) (t : ℕ) : 0 ≤ expCount π mu u k t := by
  unfold expCount
  exact MeasureTheory.integral_nonneg (fun _ => Nat.cast_nonneg _)

/-- Lemma 22 combined with `Δ ≤ Δ_uk`. -/
lemma qb8_psi_ge {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K)
    (lam : Fin U → ℝ) (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hlam : ∀ u, 0 ≤ lam u ∧ lam u ≤ 1) (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1)
    (hA1 : Assumption1 mu kstar) (hA2 : ∀ u, 0 < eps lam mu kstar u)
    (π : Policy U K) (u : Fin U) (t : ℕ) :
    gapMin mu kstar * ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
        expCount π mu u k t - eps lam mu kstar u * t ≤
      queueRegret lam mu kstar (initLaw lam mu kstar) π u t := by
  have h22 := lemma_22 hUK hK lam mu kstar hlam hmu hA1 hA2 π u t
  have : gapMin mu kstar * ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
        expCount π mu u k t ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
        gap mu kstar u k * expCount π mu u k t := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (qb8_gapMin_le mu kstar u k (Finset.mem_filter.1 hk).2)
      (qb8_expCount_nonneg π mu u k t)
  linarith

theorem solution {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (hU : 0 < U)
    (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) (hA1 : QueueBandit.LateLower.Assumption1 mu kstar)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (π : QueueBandit.LateLower.Policy U K)
    (hπ : QueueBandit.LateLower.IsAlphaConsistent π α)
    (γ : ℝ) (hγ : 1 / (1 - α) < γ) :
    ∃ τ C₁ : ℝ, Real.exp 1 < τ ∧ 0 < C₁ ∧
      ∀ lam : Fin U → ℝ, (∀ u, 0 ≤ lam u ∧ lam u ≤ 1) → (∀ u, 0 < eps lam mu kstar u) →
        let T₀ : ℝ := max (C₁ * (K : ℝ) ^ γ) τ
        let η : ℝ := ((K : ℝ) - 1) * QueueBandit.LateLower.D mu kstar / (2 * T₀)
        let εbar : ℝ := (1 / (U : ℝ)) * ∑ u : Fin U, eps lam mu kstar u
        (εbar < η / 2 → ∀ t : ℕ, T₀ ≤ t →
          (t : ℝ) ≤ ((K : ℝ) - 1) * QueueBandit.LateLower.D mu kstar / (4 * εbar) →
          QueueBandit.LateLower.D mu kstar / 4 * ((K : ℝ) - 1) *
              (Real.log t / Real.log (Real.log t)) ≤
            (1 / (U : ℝ)) * ∑ u : Fin U,
              QueueBandit.LateLower.queueRegret lam mu kstar (initLaw lam mu kstar) π u t) ∧
        (∀ u : Fin U, eps lam mu kstar u < η → ∀ t : ℕ, T₀ ≤ t →
          (t : ℝ) ≤ ((K : ℝ) - 1) * QueueBandit.LateLower.D mu kstar / (2 * eps lam mu kstar u) →
          QueueBandit.LateLower.D mu kstar / 4 * max ((U : ℝ) - 1) (2 * ((K : ℝ) - U)) *
              (Real.log t / Real.log (Real.log t)) ≤
            QueueBandit.LateLower.queueRegret lam mu kstar (initLaw lam mu kstar) π u t) := by
  obtain ⟨τc, C, hC, hcor⟩ := QueueBandit.EarlyLower.corollary_20 hUK hK hU mu kstar hmu hA1 α
    hα0 hα1 π hπ
  obtain ⟨B, hB, hBt⟩ := qb8_eventually (1 - α) (Real.log (4 * K * C)) (by linarith)
  set τ : ℝ := max (max (Real.exp B) ((τc : ℝ) + 1)) (Real.exp 1 + 1) with hτ
  refine ⟨τ, 1, lt_of_lt_of_le (by linarith) (le_max_right _ _), one_pos, ?_⟩
  intro lam hlam heps T₀ η εbar
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hUr : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hUKr : (U : ℝ) ≤ K := by exact_mod_cast hUK
  have hτT : τ ≤ T₀ := le_max_right _ _
  have hτpos : 0 < τ := lt_of_lt_of_le (by linarith [Real.exp_pos 1]) (le_max_right _ _)
  have hT₀pos : 0 < T₀ := lt_of_lt_of_le hτpos hτT
  have hgm := qb8_gapMin_nonneg mu kstar hA1
  -- facts valid for every `t ≥ T₀`
  have htfacts : ∀ t : ℕ, T₀ ≤ t → 0 < (t : ℝ) ∧ τc < t ∧
      6 ≤ 2 * ((1 - α) * Real.log t - Real.log (4 * K * C)) -
        Real.log t / Real.log (Real.log t) := by
    intro t ht
    have htτ : τ ≤ (t : ℝ) := le_trans hτT ht
    have htpos : 0 < (t : ℝ) := lt_of_lt_of_le hτpos htτ
    refine ⟨htpos, ?_, ?_⟩
    · have : (τc : ℝ) + 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) htτ
      have : (τc : ℝ) < t := by linarith
      exact_mod_cast this
    · apply hBt
      exact (Real.le_log_iff_exp_le htpos).2
        (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) htτ)
  refine ⟨?_, ?_⟩
  · -- part (a)
    intro hε t ht htle
    obtain ⟨htpos, htc, hkey⟩ := htfacts t ht
    obtain ⟨hca, -, -⟩ := hcor t htc
    set L := (1 - α) * Real.log t - Real.log (4 * K * C) with hL
    set R := Real.log t / Real.log (Real.log t) with hR
    set S := ∑ u : Fin U, ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
        expCount π mu u k t with hS
    have hεpos : 0 < εbar := by
      have : 0 < ∑ u : Fin U, eps lam mu kstar u :=
        Finset.sum_pos (fun u _ => heps u) ⟨⟨0, hU⟩, Finset.mem_univ _⟩
      positivity
    have hDpos : 0 < D mu kstar := by
      by_contra hD
      push Not at hD
      have : η ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hD
        · linarith
      linarith
    have hX : (1 / (U : ℝ)) * (gapMin mu kstar * S) - εbar * t ≤
        (1 / (U : ℝ)) * ∑ u : Fin U, queueRegret lam mu kstar (initLaw lam mu kstar) π u t := by
      have hsum := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset (Fin U))) =>
        qb8_psi_ge hUK hK lam mu kstar hlam hmu hA1 heps π u t)
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hsum
      have hU0 : (0 : ℝ) < 1 / (U : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left hsum hU0.le
      have heq : εbar * t = (1 / (U : ℝ)) * ((∑ u : Fin U, eps lam mu kstar u) * t) := by
        simp only [εbar]; ring
      rw [heq]; rw [hS]; linarith
    have hgS : ((K : ℝ) - 1) * D mu kstar * L / 2 ≤ (1 / (U : ℝ)) * (gapMin mu kstar * S) := by
      have hUpos : (0 : ℝ) < U := by linarith
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hUpos]
      nlinarith
    have hεt : εbar * t ≤ ((K : ℝ) - 1) * D mu kstar / 4 := by
      rw [le_div_iff₀ (by positivity)] at htle
      linarith
    have hA : 0 < ((K : ℝ) - 1) * D mu kstar := mul_pos (by linarith) hDpos
    have : 0 ≤ ((K : ℝ) - 1) * D mu kstar * (2 * L - R - 6) :=
      mul_nonneg hA.le (by linarith)
    nlinarith
  · -- part (b)
    intro u hεu t ht htle
    obtain ⟨htpos, htc, hkey⟩ := htfacts t ht
    obtain ⟨-, hcb, hcc⟩ := hcor t htc
    have hcb := hcb u
    have hcc := hcc u
    set L := (1 - α) * Real.log t - Real.log (4 * K * C) with hL
    set R := Real.log t / Real.log (Real.log t) with hR
    set Sb := ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
        expCount π mu u k t with hSb
    set Sc := ∑ k ∈ Finset.univ.filter (fun k : Fin K => ∀ u' : Fin U, kstar u' ≠ k),
        expCount π mu u k t with hSc
    have hScb : Sc ≤ Sb := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact fun h => hk u h.symm
      · intro k _ _; exact qb8_expCount_nonneg π mu u k t
    have hepos := heps u
    have hDpos : 0 < D mu kstar := by
      by_contra hD
      push Not at hD
      have : η ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hD
        · linarith
      linarith
    have hψ := qb8_psi_ge hUK hK lam mu kstar hlam hmu hA1 heps π u t
    have hεt : eps lam mu kstar u * t ≤ ((K : ℝ) - 1) * D mu kstar / 2 := by
      rw [le_div_iff₀ (by positivity)] at htle
      linarith
    set M := max ((U : ℝ) - 1) (2 * ((K : ℝ) - U)) with hM
    have hM1 : (U : ℝ) - 1 ≤ M := le_max_left _ _
    have hM2 : 2 * ((K : ℝ) - U) ≤ M := le_max_right _ _
    have hM0 : 0 ≤ M := le_trans (by linarith) hM1
    have hMDL : M * D mu kstar * L ≤ 2 * (gapMin mu kstar * Sb) := by
      have h3 : gapMin mu kstar * Sc ≤ gapMin mu kstar * Sb :=
        mul_le_mul_of_nonneg_left hScb hgm
      rcases le_total ((U : ℝ) - 1) (2 * ((K : ℝ) - U)) with h | h
      · rw [hM, max_eq_right h]; linarith
      · rw [hM, max_eq_left h]; linarith
    rw [← hSb] at hψ
    clear_value L R Sb Sc M
    have hML : 2 * ((K : ℝ) - 1) ≤ M * (2 * L - R) := by
      have : M * 6 ≤ M * (2 * L - R) := mul_le_mul_of_nonneg_left hkey hM0
      linarith
    have : 0 ≤ D mu kstar * (M * (2 * L - R) - 2 * ((K : ℝ) - 1)) :=
      mul_nonneg hDpos.le (by linarith)
    linarith
