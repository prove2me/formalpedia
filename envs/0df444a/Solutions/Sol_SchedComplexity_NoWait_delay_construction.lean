-- Prove2me | solution 1 for SchedComplexity.NoWait.delay_construction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:55:39.39106+00:00
-- url     : https://prove2.me/submissions/ffe516ce-0f88-421d-8adc-f7cd869bf988

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_Construction



namespace SchedComplexity.NoWait

section cons
variable {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ) (lam mu : ℕ)

theorem ps_bd (ℓ : Fin n) (i : ℕ) :
    (i : ℤ) * mu - lam - 1 ≤ partialSum adj ι lam mu ℓ i ∧
      partialSum adj ι lam mu ℓ i ≤ (i : ℤ) * mu + lam + 1 := by
  have : (0:ℤ) ≤ lam := by positivity
  unfold partialSum
  split_ifs <;> constructor <;> linarith

theorem procTimes_pos_core (hι : Admissible n ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (ℓ : Fin n) (r : Fin (numMachines n)) : 1 ≤ procTimeInt adj ι lam mu ℓ r := by
  have h1 : (1:ℤ) ≤ lam := by exact_mod_cast hlam
  have h2 : (2:ℤ) * lam + 3 ≤ mu := by exact_mod_cast hmu
  unfold procTimeInt
  split_ifs with h
  · have := (ps_bd adj ι lam mu ℓ 1).1
    push_cast at this
    linarith
  · have a := (ps_bd adj ι lam mu ℓ (r.val+1)).1
    have b := (ps_bd adj ι lam mu ℓ r.val).2
    push_cast at a b
    linarith


theorem cum_succ' {m : ℕ} (p : Fin n → Fin m → ℕ) (ℓ : Fin n) (i : ℕ) (h : i < m) :
    cum p ℓ (i+1) = cum p ℓ i + p ℓ ⟨i, h⟩ := by
  unfold cum
  have : Finset.univ.filter (fun r : Fin m => r.val < i + 1) =
      insert ⟨i, h⟩ (Finset.univ.filter (fun r : Fin m => r.val < i)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem ps_zero (hι : Admissible n ι) (ℓ : Fin n) : partialSum adj ι lam mu ℓ 0 = 0 := by
  have h1 : ¬ ∃ k : Fin n, k ≠ ℓ ∧ 0 = ι ℓ k ∧ adj ℓ k = true := by
    rintro ⟨k, hk, h, _⟩
    have := (hι.1 ℓ k hk.symm).1
    omega
  have h2 : ¬ ∃ k : Fin n, k ≠ ℓ ∧ 0 = ι ℓ k ∧ adj ℓ k = false := by
    rintro ⟨k, hk, h, _⟩
    have := (hι.1 ℓ k hk.symm).1
    omega
  have h3 : ¬ ∃ j : Fin n, j ≠ ℓ ∧ 0 + 1 = ι j ℓ ∧ adj j ℓ = true := by
    rintro ⟨k, hk, h, _⟩
    have := (hι.1 k ℓ hk).1
    omega
  have h4 : ¬ ∃ j : Fin n, j ≠ ℓ ∧ 0 + 1 = ι j ℓ ∧ adj j ℓ = false := by
    rintro ⟨k, hk, h, _⟩
    have := (hι.1 k ℓ hk).1
    omega
  unfold partialSum
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  simp

theorem ps_pos_arc (hι : Admissible n ι) (j k : Fin n) (hjk : j ≠ k) (i : ℕ) (hi : i = ι j k)
    (ha : adj j k = true) : partialSum adj ι lam mu j i = (i : ℤ) * mu + lam := by
  unfold partialSum
  rw [if_pos ⟨k, hjk.symm, hi, ha⟩]

theorem ps_pos_noarc (hι : Admissible n ι) (j k : Fin n) (hjk : j ≠ k) (i : ℕ) (hi : i = ι j k)
    (ha : adj j k = false) : partialSum adj ι lam mu j i = (i : ℤ) * mu + lam + 1 := by
  have h1 : ¬ ∃ k' : Fin n, k' ≠ j ∧ i = ι j k' ∧ adj j k' = true := by
    rintro ⟨k', hk', h, hh⟩
    have := hι.2.1 j k j k' hjk hk'.symm (by omega)
    have : k = k' := this.2
    subst this
    rw [ha] at hh; exact Bool.false_ne_true hh
  unfold partialSum
  rw [if_neg h1, if_pos ⟨k, hjk.symm, hi, ha⟩]

theorem ps_neg_arc (hι : Admissible n ι) (j k : Fin n) (hjk : j ≠ k) (i : ℕ) (hi : i + 1 = ι j k)
    (ha : adj j k = true) : partialSum adj ι lam mu k i = (i : ℤ) * mu - lam := by
  have h1 : ¬ ∃ k' : Fin n, k' ≠ k ∧ i = ι k k' ∧ adj k k' = true := by
    rintro ⟨k', hk', h, _⟩
    exact hι.2.2.2 j k k' hjk hk'.symm (by omega)
  have h2 : ¬ ∃ k' : Fin n, k' ≠ k ∧ i = ι k k' ∧ adj k k' = false := by
    rintro ⟨k', hk', h, _⟩
    exact hι.2.2.2 j k k' hjk hk'.symm (by omega)
  unfold partialSum
  rw [if_neg h1, if_neg h2, if_pos ⟨j, hjk, hi, ha⟩]

theorem ps_neg_noarc (hι : Admissible n ι) (j k : Fin n) (hjk : j ≠ k) (i : ℕ) (hi : i + 1 = ι j k)
    (ha : adj j k = false) : partialSum adj ι lam mu k i = (i : ℤ) * mu - lam - 1 := by
  have h1 : ¬ ∃ k' : Fin n, k' ≠ k ∧ i = ι k k' ∧ adj k k' = true := by
    rintro ⟨k', hk', h, _⟩
    exact hι.2.2.2 j k k' hjk hk'.symm (by omega)
  have h2 : ¬ ∃ k' : Fin n, k' ≠ k ∧ i = ι k k' ∧ adj k k' = false := by
    rintro ⟨k', hk', h, _⟩
    exact hι.2.2.2 j k k' hjk hk'.symm (by omega)
  have h3 : ¬ ∃ j' : Fin n, j' ≠ k ∧ i + 1 = ι j' k ∧ adj j' k = true := by
    rintro ⟨j', hj', h, hh⟩
    have := hι.2.1 j k j' k hjk hj'.symm.symm.symm.symm (by omega)
    have : j = j' := this.1
    subst this
    rw [ha] at hh; exact Bool.false_ne_true hh
  unfold partialSum
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos ⟨j, hjk, hi, ha⟩]

theorem ps_le_of_not_pos (ℓ : Fin n) (i : ℕ) (hlam : 1 ≤ lam)
    (h : ¬ ∃ k : Fin n, k ≠ ℓ ∧ i = ι ℓ k) : partialSum adj ι lam mu ℓ i ≤ (i : ℤ) * mu := by
  have : (0:ℤ) ≤ lam := by positivity
  unfold partialSum
  split_ifs with a b c d
  · exact absurd (by obtain ⟨k, hk, h1, _⟩ := a; exact ⟨k, hk, h1⟩) h
  · exact absurd (by obtain ⟨k, hk, h1, _⟩ := b; exact ⟨k, hk, h1⟩) h
  · linarith
  · linarith
  · exact le_refl _

theorem ps_ge_of_not_neg (ℓ : Fin n) (i : ℕ) (hlam : 1 ≤ lam)
    (h : ¬ ∃ j : Fin n, j ≠ ℓ ∧ i + 1 = ι j ℓ) : (i : ℤ) * mu ≤ partialSum adj ι lam mu ℓ i := by
  have : (0:ℤ) ≤ lam := by positivity
  unfold partialSum
  split_ifs with a b c d
  · linarith
  · linarith
  · exact absurd (by obtain ⟨k, hk, h1, _⟩ := c; exact ⟨k, hk, h1⟩) h
  · exact absurd (by obtain ⟨k, hk, h1, _⟩ := d; exact ⟨k, hk, h1⟩) h
  · exact le_refl _

theorem cum_eq_ps (hι : Admissible n ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu) (ℓ : Fin n) :
    ∀ i : ℕ, i ≤ numMachines n →
      (cum (procTimes adj ι lam mu) ℓ i : ℤ) = partialSum adj ι lam mu ℓ i := by
  intro i
  induction i with
  | zero => intro _; rw [ps_zero adj ι lam mu hι]; simp [cum]
  | succ i ih =>
    intro hi
    have ih := ih (by omega)
    rw [cum_succ' (procTimes adj ι lam mu) ℓ i (by omega)]
    push_cast
    rw [ih]
    have hp := procTimes_pos_core adj ι lam mu hι hlam hmu ℓ ⟨i, by omega⟩
    have : (procTimes adj ι lam mu ℓ ⟨i, by omega⟩ : ℤ) = procTimeInt adj ι lam mu ℓ ⟨i, by omega⟩ := by
      unfold procTimes
      exact Int.toNat_of_nonneg (by omega)
    rw [this]
    unfold procTimeInt
    by_cases h0 : i = 0
    · subst h0
      simp [ps_zero adj ι lam mu hι]
    · simp only [Fin.val_mk, h0, if_false]
      ring


theorem delay_construction_core (hι : Admissible n ι) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (j k : Fin n) (hjk : j ≠ k) :
    delay (procTimes adj ι lam mu) (numMachines_pos n) j k =
      if adj j k = true then (mu : ℤ) + 2 * lam else (mu : ℤ) + 2 * lam + 2 := by
  have hl : (1:ℤ) ≤ lam := by exact_mod_cast hlam
  apply le_antisymm
  · unfold delay
    apply Finset.sup'_le
    intro r _
    have hr := r.isLt
    rw [cum_eq_ps adj ι lam mu hι hlam hmu j (r.val+1) (by omega),
      cum_eq_ps adj ι lam mu hι hlam hmu k r.val (by omega)]
    have b1 := (ps_bd adj ι lam mu j (r.val+1)).2
    have b2 := (ps_bd adj ι lam mu k r.val).1
    push_cast at b1 b2
    by_cases ha : adj j k = true
    · rw [if_pos ha]
      by_cases hP : ∃ k' : Fin n, k' ≠ j ∧ r.val + 1 = ι j k'
      · by_cases hN : ∃ j' : Fin n, j' ≠ k ∧ r.val + 1 = ι j' k
        · obtain ⟨k', hk', e1⟩ := hP
          obtain ⟨j', hj', e2⟩ := hN
          have := hι.2.1 j k' j' k hk'.symm hj' (by omega)
          obtain ⟨rfl, rfl⟩ := this
          rw [ps_pos_arc adj ι lam mu hι j k' hjk _ e1 ha,
            ps_neg_arc adj ι lam mu hι j k' hjk r.val e1 ha]
          push_cast
          linarith
        · have := ps_ge_of_not_neg adj ι lam mu k r.val hlam hN
          linarith
      · have := ps_le_of_not_pos adj ι lam mu j (r.val+1) hlam hP
        push_cast at this
        linarith
    · rw [if_neg ha]
      linarith
  · obtain ⟨r0, hr0⟩ : ∃ r0, ι j k = r0 + 1 := ⟨ι j k - 1, by have := (hι.1 j k hjk).1; omega⟩
    have hb := (hι.1 j k hjk).2
    have hr : r0 < numMachines n := by unfold numMachines; omega
    refine le_trans ?_ (Finset.le_sup' (fun r : Fin (numMachines n) =>
      (cum (procTimes adj ι lam mu) j (r.val + 1) : ℤ) - (cum (procTimes adj ι lam mu) k r.val : ℤ))
      (Finset.mem_univ (⟨r0, hr⟩ : Fin (numMachines n))))
    simp only [Fin.val_mk]
    rw [cum_eq_ps adj ι lam mu hι hlam hmu j (r0+1) (by omega),
      cum_eq_ps adj ι lam mu hι hlam hmu k r0 (by omega)]
    by_cases ha : adj j k = true
    · rw [if_pos ha, ps_pos_arc adj ι lam mu hι j k hjk (r0+1) hr0.symm ha,
        ps_neg_arc adj ι lam mu hι j k hjk r0 hr0.symm ha]
      push_cast; linarith
    · have ha' : adj j k = false := by simpa using ha
      rw [if_neg ha, ps_pos_noarc adj ι lam mu hι j k hjk (r0+1) hr0.symm ha',
        ps_neg_noarc adj ι lam mu hι j k hjk r0 hr0.symm ha']
      push_cast; linarith

end cons
end SchedComplexity.NoWait

open SchedComplexity.NoWait


theorem solution {n : ℕ} (adj : Fin n → Fin n → Bool) (ι : Fin n → Fin n → ℕ)
    (hι : Admissible n ι) (lam mu : ℕ) (hlam : 1 ≤ lam) (hmu : 2 * lam + 3 ≤ mu)
    (j k : Fin n) (hjk : j ≠ k) :
    delay (procTimes adj ι lam mu) (numMachines_pos n) j k =
      if adj j k = true then (mu : ℤ) + 2 * lam else (mu : ℤ) + 2 * lam + 2 := by
  exact delay_construction_core adj ι lam mu hι hlam hmu j k hjk
