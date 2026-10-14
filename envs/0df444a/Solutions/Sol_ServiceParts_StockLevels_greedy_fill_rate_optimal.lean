-- Prove2me | solution 1 for ServiceParts.StockLevels.greedy_fill_rate_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:36:52.073048+00:00
-- url     : https://prove2.me/submissions/44e08ca5-6713-4f26-8b78-4294ea8c9458

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems



namespace ServiceParts.StockLevels

lemma gr_fdiff (a : ℝ) (s : ℕ) :
    poissonFillRate a (s + 1) - poissonFillRate a s = poissonPmf a s := by
  simp [poissonFillRate, Finset.sum_range_succ]

lemma gr_succ (a : ℝ) (s : ℕ) :
    poissonPmf a (s + 1) = poissonPmf a s * (a / ((s : ℝ) + 1)) := by
  unfold poissonPmf
  rw [Nat.factorial_succ]
  push_cast
  have : (s.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma gr_pmf_nonneg (a : ℝ) (ha : 0 ≤ a) (s : ℕ) : 0 ≤ poissonPmf a s := by
  unfold poissonPmf; positivity

lemma gr_pmf_anti (a : ℝ) (ha : 0 ≤ a) (t : ℕ) (ht : ⌊a⌋₊ ≤ t) :
    poissonPmf a (t + 1) ≤ poissonPmf a t := by
  rw [gr_succ]
  have hlt : a < (t : ℝ) + 1 := by
    have := Nat.lt_floor_add_one a
    have h2 : ((⌊a⌋₊ : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have h1 : a / ((t : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hlt.le
  have := gr_pmf_nonneg a ha t
  nlinarith [div_nonneg ha (by positivity : (0:ℝ) ≤ (t : ℝ) + 1)]

lemma gr_unimodal (g : ℕ → ℝ) (lo q : ℕ)
    (hup : ∀ t, lo ≤ t → t < q → g t ≤ g (t + 1)) (hdown : ∀ t, q ≤ t → g (t + 1) ≤ g t) :
    ∀ s, lo ≤ s → g s ≤ g q := by
  have hA : ∀ n, g (q + n) ≤ g q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [← add_assoc]; exact le_trans (hdown _ (by omega)) ih
  have hB : ∀ n s, lo ≤ s → s + n = q → g s ≤ g q := by
    intro n
    induction n with
    | zero => intro s _ h; simp at h; rw [h]
    | succ n ih =>
      intro s hs h
      exact le_trans (hup s hs (by omega)) (ih (s + 1) (by omega) (by omega))
  intro s hs
  rcases le_or_gt q s with h | h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    exact hA n
  · exact hB (q - s) s hs (by omega)

theorem greedy_fill_rate_optimal_core {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (lam tbar c : ι → ℝ) (hlam : ∀ i, 0 < lam i) (htbar : ∀ i, 0 < tbar i)
    (hc : ∀ i, 0 < c i) (seq : ℕ → ι → ℕ) (hseq : IsGreedySeq lam tbar c seq) (k : ℕ) :
    (∀ i, ⌊lam i * tbar i⌋₊ ≤ seq k i) ∧
    ∀ s : ι → ℕ, (∀ i, ⌊lam i * tbar i⌋₊ ≤ s i) →
      ∑ i, c i * (s i : ℝ) ≤ ∑ i, c i * (seq k i : ℝ) →
      avgFillRate lam tbar s ≤ avgFillRate lam tbar (seq k) := by
  obtain ⟨h0, hstep⟩ := hseq
  have hL : 0 < ∑ j, lam j := Finset.sum_pos (fun j _ => hlam j) Finset.univ_nonempty
  have ha : ∀ i, 0 ≤ lam i * tbar i := fun i => (mul_pos (hlam i) (htbar i)).le
  have hwt : ∀ i, 0 < lam i / ∑ j, lam j := fun i => div_pos (hlam i) hL
  have hr : ∀ i t, greedyRatio lam tbar c i t =
      lam i / (∑ j, lam j) * (poissonPmf (lam i * tbar i) t / c i) := by
    intro i t; unfold greedyRatio; rw [gr_fdiff]
  have hnn : ∀ i t, 0 ≤ greedyRatio lam tbar c i t := by
    intro i t; rw [hr]
    exact mul_nonneg (hwt i).le (div_nonneg (gr_pmf_nonneg _ (ha i) t) (hc i).le)
  have hanti1 : ∀ i t, ⌊lam i * tbar i⌋₊ ≤ t →
      greedyRatio lam tbar c i (t + 1) ≤ greedyRatio lam tbar c i t := by
    intro i t ht; rw [hr, hr]
    apply mul_le_mul_of_nonneg_left _ (hwt i).le
    exact div_le_div_of_nonneg_right (gr_pmf_anti _ (ha i) t ht) (hc i).le
  have hanti : ∀ i t t', ⌊lam i * tbar i⌋₊ ≤ t → t ≤ t' →
      greedyRatio lam tbar c i t' ≤ greedyRatio lam tbar c i t := by
    intro i t t' ht htt'
    induction t', htt' using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact le_trans (hanti1 i n (le_trans ht hn)) ih
  have hupd : ∀ k i, ∃ istar, seq (k + 1) i = (if i = istar then seq k i + 1 else seq k i) ∧
      (∀ j, greedyRatio lam tbar c j (seq k j) ≤ greedyRatio lam tbar c istar (seq k istar)) := by
    intro k i
    obtain ⟨istar, hmax, heq⟩ := hstep k
    refine ⟨istar, ?_, hmax⟩
    rw [heq, Function.update_apply]
    split_ifs with h
    · subst h; rfl
    · rfl
  have hmono : ∀ k i, seq k i ≤ seq (k + 1) i := by
    intro k i
    obtain ⟨istar, h, _⟩ := hupd k i
    rw [h]; split_ifs <;> omega
  have hfloor : ∀ k i, ⌊lam i * tbar i⌋₊ ≤ seq k i := by
    intro k i
    induction k with
    | zero => rw [h0]
    | succ k ih => exact le_trans ih (hmono k i)
  refine ⟨hfloor k, ?_⟩
  -- the max ratio
  let M : ℕ → ℝ := fun k => Finset.univ.sup' Finset.univ_nonempty
    (fun i => greedyRatio lam tbar c i (seq k i))
  have hMle : ∀ k i, greedyRatio lam tbar c i (seq k i) ≤ M k := fun k i =>
    Finset.le_sup' (f := fun i => greedyRatio lam tbar c i (seq k i)) (Finset.mem_univ i)
  have hMeq : ∀ k, ∃ istar, M k = greedyRatio lam tbar c istar (seq k istar) ∧
      seq (k + 1) = Function.update (seq k) istar (seq k istar + 1) := by
    intro k
    obtain ⟨istar, hmax, heq⟩ := hstep k
    refine ⟨istar, le_antisymm ?_ (hMle k istar), heq⟩
    exact Finset.sup'_le _ _ (fun j _ => hmax j)
  have hMdec : ∀ k, M (k + 1) ≤ M k := by
    intro k
    obtain ⟨istar, hM, heq⟩ := hMeq k
    apply Finset.sup'_le
    intro i _
    rw [heq, Function.update_apply]
    split_ifs with h
    · subst h; rw [hM]; exact hanti1 _ _ (hfloor k _)
    · exact hMle k i
  have hinv : ∀ k i t, ⌊lam i * tbar i⌋₊ ≤ t → t < seq k i →
      M k ≤ greedyRatio lam tbar c i t := by
    intro k
    induction k with
    | zero => intro i t ht hlt; rw [h0] at hlt; omega
    | succ k ih =>
      intro i t ht hlt
      rcases lt_or_ge t (seq k i) with h | h
      · exact le_trans (hMdec k) (ih i t ht h)
      · obtain ⟨istar, hM, heq⟩ := hMeq k
        rw [heq, Function.update_apply] at hlt
        split_ifs at hlt with hi
        · subst hi
          have : t = seq k i := by omega
          rw [this, ← hM]; exact hMdec k
        · omega
  have hM0 : 0 ≤ M k := le_trans (hnn _ _) (hMle k (Classical.arbitrary ι))
  intro s hs hbud
  -- per item
  have hitem : ∀ i, lam i / (∑ j, lam j) * poissonFillRate (lam i * tbar i) (s i) - M k * (c i * s i)
      ≤ lam i / (∑ j, lam j) * poissonFillRate (lam i * tbar i) (seq k i)
        - M k * (c i * seq k i) := by
    intro i
    have hstepg : ∀ t, (lam i / (∑ j, lam j) * poissonFillRate (lam i * tbar i) (t + 1)
        - M k * (c i * ((t + 1 : ℕ) : ℝ))) -
        (lam i / (∑ j, lam j) * poissonFillRate (lam i * tbar i) t - M k * (c i * (t : ℝ)))
        = c i * (greedyRatio lam tbar c i t - M k) := by
      intro t
      rw [hr]
      have h1 := gr_fdiff (lam i * tbar i) t
      have hci := (hc i).ne'
      push_cast
      have e : c i * (lam i / (∑ j, lam j) * (poissonPmf (lam i * tbar i) t / c i)) =
          lam i / (∑ j, lam j) * poissonPmf (lam i * tbar i) t := by field_simp
      linear_combination (lam i / (∑ j, lam j)) * h1 - e
    apply gr_unimodal (fun t => lam i / (∑ j, lam j) * poissonFillRate (lam i * tbar i) t
      - M k * (c i * (t : ℝ))) ⌊lam i * tbar i⌋₊ (seq k i) _ _ (s i) (hs i)
    · intro t ht hlt
      have := hstepg t
      have h2 := hinv k i t ht hlt
      have := mul_nonneg (hc i).le (sub_nonneg.mpr h2)
      linarith
    · intro t ht
      have := hstepg t
      have h2 : greedyRatio lam tbar c i t ≤ M k :=
        le_trans (hanti i (seq k i) t (hfloor k i) ht) (hMle k i)
      have := mul_nonneg (hc i).le (sub_nonneg.mpr h2)
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hitem i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  unfold avgFillRate
  nlinarith [mul_le_mul_of_nonneg_left hbud hM0]

end ServiceParts.StockLevels

open ServiceParts.StockLevels


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (lam tbar c : ι → ℝ) (hlam : ∀ i, 0 < lam i) (htbar : ∀ i, 0 < tbar i)
    (hc : ∀ i, 0 < c i) (seq : ℕ → ι → ℕ) (hseq : IsGreedySeq lam tbar c seq) (k : ℕ) :
    (∀ i, ⌊lam i * tbar i⌋₊ ≤ seq k i) ∧
    ∀ s : ι → ℕ, (∀ i, ⌊lam i * tbar i⌋₊ ≤ s i) →
      ∑ i, c i * (s i : ℝ) ≤ ∑ i, c i * (seq k i : ℝ) →
      avgFillRate lam tbar s ≤ avgFillRate lam tbar (seq k) := by
  exact greedy_fill_rate_optimal_core lam tbar c hlam htbar hc seq hseq k
