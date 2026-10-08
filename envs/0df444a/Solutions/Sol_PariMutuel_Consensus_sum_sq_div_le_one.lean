-- Prove2me | solution 1 for PariMutuel.Consensus.sum_sq_div_le_one
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T12:19:16.516795+00:00
-- url     : https://prove2.me/submissions/dd0d1675-c8ee-457b-979a-f979fea6eb17

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market



namespace PariMutuel.Consensus

open Finset

theorem pm_prob_pos {m n : ℕ} (M : Market m n) (π : Fin n → ℝ) (β : Fin m → Fin n → ℝ)
    (h : M.IsEquilibrium π β) (j : Fin n) : 0 < π j := by
  obtain ⟨hπ, hβ, hb, hc, hq⟩ := h
  rcases (hπ j).lt_or_eq with h1 | h1
  · exact h1
  exfalso
  obtain ⟨i, hi⟩ := M.P_col_pos j
  have : ∃ s, 0 < β i s := by
    by_contra hne
    push_neg at hne
    have : ∑ s, β i s ≤ 0 := Finset.sum_nonpos (fun s _ => hne s)
    have := M.b_pos i
    linarith [hb i]
  obtain ⟨s, hs⟩ := this
  have h2 := hq i s hs j
  rw [← h1] at h2
  have h3 : β i s ≤ π s := by
    rw [← hc s]
    exact Finset.single_le_sum (f := fun i => β i s) (fun i _ => hβ i s) (Finset.mem_univ i)
  have : 0 < M.P i j * π s := mul_pos hi (by linarith)
  linarith

theorem pm_sum_one {m n : ℕ} (M : Market m n) (π : Fin n → ℝ) (β : Fin m → Fin n → ℝ)
    (h : M.IsEquilibrium π β) : ∑ k, π k = 1 := by
  obtain ⟨hπ, hβ, hb, hc, hq⟩ := h
  simp_rw [← hc]
  rw [Finset.sum_comm]
  simp_rw [hb]
  exact M.b_sum

theorem pm_cs {n : ℕ} (π π' : Fin n → ℝ) (hπ : ∀ k, 0 < π k)
    (hs : ∑ k, π k = 1) (hs' : ∑ k, π' k = 1)
    (h : ∑ k, π' k * π' k / π k ≤ 1) : π' = π := by
  have key : ∑ k, (π' k - π k) ^ 2 / π k = ∑ k, π' k * π' k / π k - 1 := by
    have : ∀ k, (π' k - π k) ^ 2 / π k = π' k * π' k / π k - 2 * π' k + π k := by
      intro k
      have := (hπ k).ne'
      field_simp
      ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, hs']
    ring
  have hle : ∑ k, (π' k - π k) ^ 2 / π k ≤ 0 := by linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => div_nonneg (sq_nonneg _) (hπ k).le)).1
    (le_antisymm hle (Finset.sum_nonneg (fun k _ => div_nonneg (sq_nonneg _) (hπ k).le)))
  funext k
  have := hz k (Finset.mem_univ k)
  rw [div_eq_zero_iff] at this
  rcases this with h1 | h1
  · nlinarith [sq_nonneg (π' k - π k)]
  · exact absurd h1 (hπ k).ne'

theorem pm_sumsq {m n : ℕ} (M : Market m n) (π π' : Fin n → ℝ)
    (β β' : Fin m → Fin n → ℝ) (h : M.IsEquilibrium π β) (h' : M.IsEquilibrium π' β') :
    ∑ k, π' k * π' k / π k ≤ 1 := by
  have hp := pm_prob_pos M π β h
  have hp' := pm_prob_pos M π' β' h'
  have hs' := pm_sum_one M π' β' h'
  obtain ⟨-, hβ, hb, hc, hq⟩ := h
  obtain ⟨-, hβ', hb', hc', hq'⟩ := h'
  rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with hn | hn
  · rw [hn, Finset.sum_empty]; norm_num
  set μ : Fin m → ℝ := fun i => Finset.univ.sup' hn (fun s => M.P i s / π s) with hμ
  set μ' : Fin m → ℝ := fun i => Finset.univ.sup' hn (fun s => M.P i s / π' s) with hμ'
  have ha : ∀ i s, M.P i s ≤ μ i * π s := by
    intro i s
    have : M.P i s / π s ≤ μ i := Finset.le_sup' (fun s => M.P i s / π s) (Finset.mem_univ s)
    rwa [div_le_iff₀ (hp s)] at this
  have ha' : ∀ i s, M.P i s ≤ μ' i * π' s := by
    intro i s
    have : M.P i s / π' s ≤ μ' i := Finset.le_sup' (fun s => M.P i s / π' s) (Finset.mem_univ s)
    rwa [div_le_iff₀ (hp' s)] at this
  have hbb : ∀ i k, 0 < β i k → μ i * π k ≤ M.P i k := by
    intro i k hk
    have : μ i ≤ M.P i k / π k := by
      apply Finset.sup'_le
      intro s _
      rw [div_le_div_iff₀ (hp s) (hp k)]
      exact hq i k hk s
    rwa [le_div_iff₀ (hp k)] at this
  have hbb' : ∀ i k, 0 < β' i k → μ' i * π' k ≤ M.P i k := by
    intro i k hk
    have : μ' i ≤ M.P i k / π' k := by
      apply Finset.sup'_le
      intro s _
      rw [div_le_div_iff₀ (hp' s) (hp' k)]
      exact hq' i k hk s
    rwa [le_div_iff₀ (hp' k)] at this
  have hμ'pos : ∀ i, 0 < μ' i := by
    intro i
    have h1 : ∑ s, M.P i s ≤ ∑ s, μ' i * π' s := Finset.sum_le_sum (fun s _ => ha' i s)
    rw [M.P_row_sum, ← Finset.mul_sum, hs'] at h1
    linarith
  -- step 1
  have e1 : ∑ k, π' k * π' k / π k = ∑ i, ∑ k, β' i k * (π' k / π k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_mul, hc']
    ring
  have s1 : ∀ i, ∑ k, β' i k * (π' k / π k) ≤ M.b i * (μ i / μ' i) := by
    intro i
    rw [← hb' i, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    rcases (hβ' i k).lt_or_eq with hk | hk
    · apply mul_le_mul_of_nonneg_left _ (hβ' i k)
      rw [div_le_div_iff₀ (hp k) (hμ'pos i)]
      have := hbb' i k hk
      have := ha i k
      nlinarith
    · rw [← hk]; simp
  have s2 : ∀ i, M.b i * (μ i / μ' i) ≤ ∑ k, β i k * (π' k / π k) := by
    intro i
    rw [← hb i, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    rcases (hβ i k).lt_or_eq with hk | hk
    · apply mul_le_mul_of_nonneg_left _ (hβ i k)
      rw [div_le_div_iff₀ (hμ'pos i) (hp k)]
      have := hbb i k hk
      have := ha' i k
      nlinarith
    · rw [← hk]; simp
  have e2 : ∑ i, ∑ k, β i k * (π' k / π k) = 1 := by
    rw [Finset.sum_comm, ← hs']
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_mul, hc k]
    field_simp [(hp k).ne']
  calc ∑ k, π' k * π' k / π k = ∑ i, ∑ k, β' i k * (π' k / π k) := e1
    _ ≤ ∑ i, M.b i * (μ i / μ' i) := Finset.sum_le_sum (fun i _ => s1 i)
    _ ≤ ∑ i, ∑ k, β i k * (π' k / π k) := Finset.sum_le_sum (fun i _ => s2 i)
    _ = 1 := e2

theorem pm_unique {m n : ℕ} (M : Market m n) (π π' : Fin n → ℝ)
    (β β' : Fin m → Fin n → ℝ) (h : M.IsEquilibrium π β) (h' : M.IsEquilibrium π' β') :
    π = π' :=
  (pm_cs π π' (pm_prob_pos M π β h) (pm_sum_one M π β h) (pm_sum_one M π' β' h')
    (pm_sumsq M π π' β β' h h')).symm

end PariMutuel.Consensus

open PariMutuel.Consensus


theorem solution {m n : ℕ} (M : Market m n) (π π' : Fin n → ℝ)
    (β β' : Fin m → Fin n → ℝ) (h : M.IsEquilibrium π β) (h' : M.IsEquilibrium π' β') :
    ∑ k, π' k * π' k / π k ≤ 1 := by
  exact pm_sumsq M π π' β β' h h'
