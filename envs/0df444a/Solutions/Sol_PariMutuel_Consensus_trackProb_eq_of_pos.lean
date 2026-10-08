-- Prove2me | solution 1 for PariMutuel.Consensus.trackProb_eq_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:03:49.362974+00:00
-- url     : https://prove2.me/submissions/e72987b0-90e5-4732-a5c5-b7e2a96bed58

import Mathlib
import Definitions.Def_PariMutuel_Consensus_Market
import Definitions.Def_PariMutuel_Consensus_Phi

namespace PMC9

lemma log_sub_ge {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y - x) / y ≤ Real.log y - Real.log x := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne', inv_div] at h
  have e : (y - x) / y = 1 - x / y := by field_simp
  rw [e]; exact h

open PariMutuel.Consensus in
theorem key {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) (i : Fin m) (j : Fin n) (hij : 0 < ξ i j) (k : Fin m) :
    M.b k * M.P k j / ∑ s, M.P k s * ξ k s ≤ M.b i * M.P i j / ∑ s, M.P i s * ξ i s := by
  obtain ⟨⟨hD0, hD1⟩, hSpos0, hmax⟩ := hξ
  obtain ⟨S, hS⟩ : ∃ S : Fin m → ℝ, ∀ l, S l = ∑ s, M.P l s * ξ l s := ⟨_, fun _ => rfl⟩
  have hSpos : ∀ l, 0 < S l := fun l => by rw [hS l]; exact hSpos0 l
  rw [← hS k, ← hS i]
  have hSi := hSpos i
  have hSk := hSpos k
  by_contra hlt
  push Not at hlt
  have hki : k ≠ i := by rintro rfl; exact lt_irrefl _ hlt
  have hPij := M.P_nonneg i j
  have hPkj := M.P_nonneg k j
  have hbi := M.b_pos i
  have hbk := M.b_pos k
  have hG : 0 < M.b k * M.P k j * S i - M.b i * M.P i j * S k := by
    rw [div_lt_div_iff₀ hSi hSk] at hlt; linarith
  obtain ⟨G, hGdef⟩ : ∃ G, G = M.b k * M.P k j * S i - M.b i * M.P i j * S k := ⟨_, rfl⟩
  rw [← hGdef] at hG
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = M.P i j * M.P k j * (M.b i + M.b k) := ⟨_, rfl⟩
  have hQ : 0 ≤ Q := by rw [hQdef]; positivity
  obtain ⟨t, ht, ht1, htQ⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ξ i j / 2 ∧ t * Q < G := by
    refine ⟨min (ξ i j / 2) (G / (Q + 1)), lt_min (by linarith) (div_pos hG (by linarith)),
      min_le_left _ _, ?_⟩
    have h2 : min (ξ i j / 2) (G / (Q + 1)) ≤ G / (Q + 1) := min_le_right _ _
    have h3 : 0 < min (ξ i j / 2) (G / (Q + 1)) := lt_min (by linarith) (div_pos hG (by linarith))
    calc min (ξ i j / 2) (G / (Q + 1)) * Q ≤ G / (Q + 1) * Q := by
          exact mul_le_mul_of_nonneg_right h2 hQ
      _ < G := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  -- S i ≥ P i j * ξ i j
  have hSi_ge : M.P i j * ξ i j ≤ S i := by
    rw [hS i]
    exact Finset.single_le_sum (f := fun s => M.P i s * ξ i s)
      (fun s _ => mul_nonneg (M.P_nonneg i s) (hD0 i s)) (Finset.mem_univ j)
  obtain ⟨η, hη⟩ : ∃ η : Fin m → Fin n → ℝ, ∀ l s, η l s = ξ l s +
      (if s = j then ((if l = k then t else 0) - (if l = i then t else 0)) else 0) :=
    ⟨_, fun _ _ => rfl⟩
  have hrow : ∀ l, ∑ s, M.P l s * η l s =
      S l + ((if l = k then t else 0) - (if l = i then t else 0)) * M.P l j := by
    intro l
    simp only [hη, mul_add, Finset.sum_add_distrib, hS l]
    congr 1
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hηD : η ∈ D m n := by
    refine ⟨?_, ?_⟩
    · intro l s
      rw [hη]
      have := hD0 l s
      by_cases hs : s = j
      · subst hs
        by_cases hl : l = i
        · subst hl
          simp only [if_true, if_neg hki.symm]
          linarith
        · by_cases hlk : l = k
          · rw [hlk] at this; simp only [if_true, hlk, if_neg hki]; linarith
          · simp only [if_true, if_neg hl, if_neg hlk]; linarith
      · simp only [if_neg hs]; linarith
    · intro s
      simp only [hη, Finset.sum_add_distrib, hD1 s]
      by_cases hs : s = j
      · simp only [hs, if_true, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
        ring
      · simp only [if_neg hs, Finset.sum_const_zero, add_zero]
  have hrowi : ∑ s, M.P i s * η i s = S i - t * M.P i j := by
    rw [hrow i]; simp only [if_neg hki.symm, if_true]; ring
  have hrowk : ∑ s, M.P k s * η k s = S k + t * M.P k j := by
    rw [hrow k]; simp only [if_neg hki, if_true]; ring
  have hrowl : ∀ l, l ≠ i ∧ l ≠ k → ∑ s, M.P l s * η l s = S l := by
    intro l ⟨h1, h2⟩
    rw [hrow l]; simp only [if_neg h1, if_neg h2]; ring
  have hSi' : 0 < S i - t * M.P i j := by nlinarith
  have hSk' : 0 < S k + t * M.P k j := by nlinarith
  have hηpos : ∀ l, 0 < ∑ s, M.P l s * η l s := by
    intro l
    by_cases h1 : l = i
    · subst h1; rw [hrowi]; exact hSi'
    · by_cases h2 : l = k
      · subst h2; rw [hrowk]; exact hSk'
      · rw [hrowl l ⟨h1, h2⟩]; exact hSpos l
  have hle := hmax η hηD hηpos
  -- compute phi η - phi ξ
  have hdiff : M.phi η - M.phi ξ =
      M.b i * (Real.log (S i - t * M.P i j) - Real.log (S i)) +
      M.b k * (Real.log (S k + t * M.P k j) - Real.log (S k)) := by
    unfold Market.phi
    rw [← Finset.sum_sub_distrib]
    rw [Fintype.sum_eq_add i k hki.symm]
    · rw [hrowi, hrowk, ← hS i, ← hS k]; ring
    · intro l hl
      rw [hrowl l hl, ← hS l]; ring
  have hi := log_sub_ge hSi hSi'
  have hk := log_sub_ge hSk hSk'
  have ei : (S i - t * M.P i j - S i) / (S i - t * M.P i j) = -(t * M.P i j) / (S i - t * M.P i j) := by
    ring
  have ek : (S k + t * M.P k j - S k) / (S k + t * M.P k j) = (t * M.P k j) / (S k + t * M.P k j) := by
    ring
  rw [ei] at hi
  rw [ek] at hk
  have hi2 := mul_le_mul_of_nonneg_left hi hbi.le
  have hk2 := mul_le_mul_of_nonneg_left hk hbk.le
  have hpos : 0 < M.b i * (-(t * M.P i j) / (S i - t * M.P i j)) +
      M.b k * ((t * M.P k j) / (S k + t * M.P k j)) := by
    have e : M.b i * (-(t * M.P i j) / (S i - t * M.P i j)) +
        M.b k * ((t * M.P k j) / (S k + t * M.P k j)) =
        t * (G - t * Q) / ((S i - t * M.P i j) * (S k + t * M.P k j)) := by
      rw [hGdef, hQdef]
      field_simp
      ring
    rw [e]
    apply div_pos
    · apply mul_pos ht; linarith
    · exact mul_pos hSi' hSk'
  linarith

end PMC9

open PariMutuel.Consensus in
theorem solution {m n : ℕ} (M : Market m n) (ξ : Fin m → Fin n → ℝ)
    (hξ : M.IsPhiMaximizer ξ) (i : Fin m) (j : Fin n) (hij : 0 < ξ i j) :
    M.trackProb ξ j = M.b i * M.P i j / ∑ s, M.P i s * ξ i s := by
  unfold Market.trackProb
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun k _ => PMC9.key M ξ hξ i j hij k)
  · exact Finset.le_sup' (fun l => M.b l * M.P l j / ∑ s, M.P l s * ξ l s) (Finset.mem_univ i)
