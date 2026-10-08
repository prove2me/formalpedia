-- Prove2me | solution 1 for TalagrandConc.BinPacking.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:26:29.467684+00:00
-- url     : https://prove2.me/submissions/be228e57-9269-419e-8472-0b200d6a8869

import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic



namespace TalagrandConc.BinPacking

open scoped ENNReal

/-- A packing of the items in `I` only. -/
def PackingOn {N : ℕ} (I : Finset (Fin N)) (x : Fin N → unitInterval) (k : ℕ) : Prop :=
  ∃ σ : Fin N → Fin k, ∀ j : Fin k,
    ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) ≤ 1

lemma packingOn_univ_iff {N : ℕ} (x : Fin N → unitInterval) (k : ℕ) :
    PackingOn Finset.univ x k ↔ IsPacking x k := Iff.rfl

lemma sum_filter_insert {N k : ℕ} (x : Fin N → unitInterval) (I : Finset (Fin N)) (a : Fin N)
    (ha : a ∉ I) (σ : Fin N → Fin k) (j : Fin k) :
    ∑ i ∈ (insert a I).filter (fun i => σ i = j), (x i : ℝ) =
      (if σ a = j then (x a : ℝ) else 0) + ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) := by
  classical
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert]
    simp only [Finset.mem_filter, not_and]; intro h'; exact absurd h' ha
  · rw [zero_add]

lemma sum_filter_congr {N k : ℕ} (x : Fin N → unitInterval) (I : Finset (Fin N))
    (σ σ' : Fin N → Fin k) (h : ∀ i ∈ I, σ' i = σ i) (j : Fin k) :
    ∑ i ∈ I.filter (fun i => σ' i = j), (x i : ℝ) = ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) := by
  classical
  congr 1
  apply Finset.filter_congr; intro i hi; rw [h i hi]

/-- Key greedy lemma: there is a packing of the items of `I` into `k` bins whose pairwise
bin sums exceed one. -/
lemma exists_packingOn_pairwise {N : ℕ} (x : Fin N → unitInterval) (I : Finset (Fin N)) :
    ∃ k : ℕ, ∃ σ : Fin N → Fin k,
      (∀ j : Fin k, ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) ≤ 1) ∧
      (∀ j j' : Fin k, j ≠ j' →
        1 < ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) +
            ∑ i ∈ I.filter (fun i => σ i = j'), (x i : ℝ)) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 0, fun j => by simp, fun j j' hjj' => absurd (Subsingleton.elim j j') hjj'⟩
  | insert a I ha ih =>
    obtain ⟨k, σ, hσ1, hσ2⟩ := ih
    have hx0 : 0 ≤ (x a : ℝ) := (x a).2.1
    have hx1 : (x a : ℝ) ≤ 1 := (x a).2.2
    by_cases hfit : ∃ j : Fin k, ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) + (x a : ℝ) ≤ 1
    · obtain ⟨j₀, hj₀⟩ := hfit
      have hupd : ∀ i ∈ I, Function.update σ a j₀ i = σ i :=
        fun i hi => Function.update_of_ne (fun h : i = a => ha (h ▸ hi)) _ _
      refine ⟨k, Function.update σ a j₀, ?_, ?_⟩
      · intro j
        rw [sum_filter_insert x I a ha, sum_filter_congr x I σ _ hupd]
        simp only [Function.update_self]
        split_ifs with h
        · subst h; linarith
        · simpa using hσ1 j
      · intro j j' hjj'
        rw [sum_filter_insert x I a ha, sum_filter_congr x I σ _ hupd,
          sum_filter_insert x I a ha, sum_filter_congr x I σ _ hupd]
        have := hσ2 j j' hjj'
        simp only [Function.update_self]
        split_ifs <;> linarith
    · push_neg at hfit
      -- new bin
      set σ' : Fin N → Fin (k + 1) := fun i => if i = a then Fin.last k else Fin.castSucc (σ i)
        with hσ'
      have hσ'a : σ' a = Fin.last k := by simp [hσ']
      have hcast : ∀ j : Fin k, ∑ i ∈ I.filter (fun i => σ' i = Fin.castSucc j), (x i : ℝ) =
          ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) := by
        intro j
        congr 1
        apply Finset.filter_congr
        intro i hi
        have : i ≠ a := fun h => ha (h ▸ hi)
        simp [hσ', this, Fin.castSucc_inj]
      have hlast : ∑ i ∈ I.filter (fun i => σ' i = Fin.last k), (x i : ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_filter] at hi
        exfalso
        have : i ≠ a := fun h => ha (h ▸ hi.1)
        have h2 := hi.2
        simp only [hσ', this, if_false] at h2
        exact Fin.castSucc_ne_last _ h2
      refine ⟨k + 1, σ', ?_, ?_⟩
      · intro j
        rw [sum_filter_insert x I a ha, hσ'a]
        induction j using Fin.lastCases with
        | last => rw [hlast]; simp [hx1]
        | cast j => rw [hcast, if_neg (Fin.castSucc_ne_last j).symm, zero_add]; exact hσ1 j
      · intro j j' hjj'
        rw [sum_filter_insert x I a ha, sum_filter_insert x I a ha, hσ'a]
        induction j using Fin.lastCases with
        | last =>
          rw [hlast]
          induction j' using Fin.lastCases with
          | last => exact absurd rfl hjj'
          | cast j' =>
            rw [hcast, if_neg (Fin.castSucc_ne_last j').symm, if_pos rfl]
            have := hfit j'; linarith
        | cast j =>
          rw [hcast, if_neg (Fin.castSucc_ne_last j).symm]
          induction j' using Fin.lastCases with
          | last =>
            rw [hlast, if_pos rfl]
            have := hfit j; linarith
          | cast j' =>
            rw [hcast, if_neg (Fin.castSucc_ne_last j').symm]
            have : j ≠ j' := fun h => hjj' (by rw [h])
            have := hσ2 j j' this; linarith

/-- Sum of pairwise-large bins: `k ≤ 2 S + 1`. -/
lemma card_le_of_pairwise {k : ℕ} (b : Fin k → ℝ) (hb : ∀ j, 0 ≤ b j)
    (h : ∀ j j', j ≠ j' → 1 < b j + b j') : (k : ℝ) ≤ 2 * ∑ j, b j + 1 := by
  classical
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have : (k : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hk
    have : 0 ≤ ∑ j, b j := Finset.sum_nonneg (fun j _ => hb j)
    linarith
  · -- choose a minimal bin
    have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ b hne
    have hhalf : ∀ j, j ≠ j₀ → 1 / 2 < b j := by
      intro j hj
      have h1 := h j j₀ hj
      have h2 := hj₀ j (Finset.mem_univ _)
      linarith
    have hsum : ∑ j, b j = b j₀ + ∑ j ∈ Finset.univ.erase j₀, b j :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
    have hcard : ((Finset.univ.erase j₀).card : ℝ) = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      rw [Nat.cast_sub (by omega)]; simp
    have hlow : ((Finset.univ.erase j₀).card : ℝ) * (1 / 2) ≤ ∑ j ∈ Finset.univ.erase j₀, b j := by
      have := Finset.card_nsmul_le_sum (Finset.univ.erase j₀) b (1 / 2)
        (fun j hj => le_of_lt (hhalf j (Finset.ne_of_mem_erase hj)))
      simpa [nsmul_eq_mul] using this
    have := hb j₀
    rw [hcard] at hlow
    linarith


lemma sum_bins {N k : ℕ} (x : Fin N → unitInterval) (I : Finset (Fin N)) (σ : Fin N → Fin k) :
    ∑ j, ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ) = ∑ i ∈ I, (x i : ℝ) := by
  classical
  exact Finset.sum_fiberwise I σ (fun i => (x i : ℝ))

/-- Greedy packing of the items of `I`: `k ≤ 2 ∑_{i ∈ I} x_i + 1`. -/
lemma exists_packingOn_le {N : ℕ} (x : Fin N → unitInterval) (I : Finset (Fin N)) :
    ∃ k : ℕ, PackingOn I x k ∧ (k : ℝ) ≤ 2 * ∑ i ∈ I, (x i : ℝ) + 1 := by
  classical
  obtain ⟨k, σ, h1, h2⟩ := exists_packingOn_pairwise x I
  refine ⟨k, ⟨σ, h1⟩, ?_⟩
  have := card_le_of_pairwise (fun j => ∑ i ∈ I.filter (fun i => σ i = j), (x i : ℝ))
    (fun j => Finset.sum_nonneg (fun i _ => (x i).2.1)) h2
  rwa [sum_bins] at this

lemma binNumber_le_of_isPacking {N : ℕ} (x : Fin N → unitInterval) {k : ℕ} (h : IsPacking x k) :
    binNumber x ≤ k := Nat.sInf_le h

theorem lemma_6_1_core {N : ℕ} (x : Fin N → unitInterval) :
    (binNumber x : ℝ) ≤ 2 * ∑ i, (x i : ℝ) + 1 := by
  obtain ⟨k, hk, hle⟩ := exists_packingOn_le x Finset.univ
  have : binNumber x ≤ k := binNumber_le_of_isPacking x ((packingOn_univ_iff x k).mp hk)
  calc (binNumber x : ℝ) ≤ k := by exact_mod_cast this
    _ ≤ _ := hle

end TalagrandConc.BinPacking

open TalagrandConc.BinPacking


theorem solution {N : ℕ} (x : Fin N → unitInterval) :
    (binNumber x : ℝ) ≤ 2 * ∑ i, (x i : ℝ) + 1 := by
  exact lemma_6_1_core x
