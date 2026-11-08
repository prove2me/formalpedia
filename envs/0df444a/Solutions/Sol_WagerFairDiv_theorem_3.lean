-- Prove2me | solution 1 for WagerFairDiv.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:48:16.734871+00:00
-- url     : https://prove2.me/submissions/b6ae3590-2a61-4036-8b16-34bcfcaec31f

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

namespace Aux_WagerFairDiv_t3
open WagerFairDiv

lemma total_pos {n : ℕ} (w : PosVec n) (i : Fin n) : 0 < w.total := by
  unfold PosVec.total
  calc 0 < w.1 i := w.2 i
    _ ≤ ∑ k, w.1 k := Finset.single_le_sum (fun k _ => (w.2 k).le) (Finset.mem_univ i)

lemma p_nonneg {n m : ℕ} (p : Profile n m) (i : Fin n) (j : Fin m) : 0 ≤ (p i).1 j :=
  (p i).2.1 j

lemma val_add {m : ℕ} (x z z' : Fin m → ℝ) :
    val x (fun j => z j + z' j) = val x z + val x z' := by
  unfold val; simp only [mul_add, Finset.sum_add_distrib]

lemma val_mul {m : ℕ} (x z : Fin m → ℝ) (c : ℝ) :
    val x (fun j => c * z j) = c * val x z := by
  unfold val; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

lemma val_div {m : ℕ} (x z : Fin m → ℝ) (c : ℝ) :
    val x (fun j => z j / c) = val x z / c := by
  unfold val; rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring

lemma val_nonneg {m : ℕ} (x z : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j) (hz : ∀ j, 0 ≤ z j) :
    0 ≤ val x z := Finset.sum_nonneg (fun j _ => mul_nonneg (hx j) (hz j))

end Aux_WagerFairDiv_t3

open WagerFairDiv Aux_WagerFairDiv_t3 in
theorem solution {n m : ℕ} (A B : Mech n m) (hA : IsAllocMech A) (hAB : Corresponding A B) :
    ParetoOptimal A ↔ SideBetPO B ∧ BBOnSupport B := by
  classical
  constructor
  · intro hPO
    constructor
    · rintro p w ⟨db, hsum, hnn, hval, i1, hi1⟩
      have hW := total_pos w i1
      set a' : Fin n → Fin m → ℝ := fun i j => A p w i j + db i j / w.total with ha'
      have hfeas : IsFeasibleAlloc a' := by
        refine ⟨fun i j => ?_, fun j => ?_⟩
        · have h := hnn i j
          rw [hAB] at h
          have : A p w i j + db i j / w.total = (w.total * A p w i j + db i j) / w.total := by
            field_simp
          simp only [ha']
          rw [this]; exact div_nonneg h hW.le
        · simp only [ha', Finset.sum_add_distrib, ← Finset.sum_div, hsum j, zero_div, add_zero]
          exact (hA p w).2 j
      have hv : ∀ i, val (p i).1 (a' i) = val (p i).1 (A p w i) + val (p i).1 (db i) / w.total := by
        intro i
        simp only [ha']
        rw [val_add, val_div]
      obtain ⟨k, hk⟩ := hPO p w a' hfeas ⟨i1, by rw [hv]; have := div_pos hi1 hW; linarith⟩
      rw [hv] at hk
      have := div_nonneg (hval k) hW.le
      linarith
    · rintro p w j ⟨i1, hi1⟩
      have hW := total_pos w i1
      have hBsum : ∑ i, B p w i j = w.total * ∑ i, A p w i j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => hAB p w i j)
      by_contra hne
      have hle := (hA p w).2 j
      have hlt : ∑ i, A p w i j < 1 := by
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd (by rw [hBsum, h, mul_one]) hne
      set s := 1 - ∑ i, A p w i j with hs
      have hspos : 0 < s := by rw [hs]; linarith
      set a' : Fin n → Fin m → ℝ :=
        fun i j' => A p w i j' + (if i = i1 then (if j' = j then s else 0) else 0) with ha'
      have hfeas : IsFeasibleAlloc a' := by
        refine ⟨fun i j' => ?_, fun j' => ?_⟩
        · simp only [ha']
          have := (hA p w).1 i j'
          split_ifs <;> linarith
        · simp only [ha', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          split_ifs with h
          · subst h; rw [hs]; linarith
          · rw [add_zero]; exact (hA p w).2 j'
      have hv : ∀ i, val (p i).1 (a' i) = val (p i).1 (A p w i)
          + (if i = i1 then (p i).1 j * s else 0) := by
        intro i
        simp only [ha']
        rw [val_add]
        congr 1
        unfold val
        split_ifs with h
        · simp
        · simp
      obtain ⟨k, hk⟩ := hPO p w a' hfeas ⟨i1, by
        rw [hv, if_pos rfl]; have := mul_pos hi1 hspos; linarith⟩
      rw [hv] at hk
      have : 0 ≤ (if k = i1 then (p k).1 j * s else 0) := by
        split_ifs
        · exact mul_nonneg (p_nonneg p k j) hspos.le
        · exact le_rfl
      linarith
  · rintro ⟨hSB, hBB⟩ p w a' ha' ⟨i1, hi1⟩
    by_contra hno
    push_neg at hno
    have hW := total_pos w i1
    let supp : Fin m → Prop := fun j => ∃ i, 0 < (p i).1 j
    set a'' : Fin n → Fin m → ℝ := fun i j => if supp j then a' i j else A p w i j with ha''
    set c : Fin m → ℝ := fun j => w.total * (∑ i, A p w i j - ∑ i, a'' i j) with hc
    set db : Fin n → Fin m → ℝ :=
      fun i j => w.total * (a'' i j - A p w i j) + (if i = i1 then c j else 0) with hdb
    have hc0 : ∀ j, 0 ≤ c j := by
      intro j
      simp only [hc]
      by_cases hs : supp j
      · have hBs := hBB p w j hs
        have hBsum : ∑ i, B p w i j = w.total * ∑ i, A p w i j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => hAB p w i j)
        have h1 : ∑ i, A p w i j = 1 := by
          rw [hBsum] at hBs
          have := mul_left_cancel₀ hW.ne' (hBs.trans (mul_one _).symm)
          exact this
        have h2 : ∑ i, a'' i j = ∑ i, a' i j := by
          simp only [ha'', if_pos hs]
        rw [h1, h2]
        exact mul_nonneg hW.le (by linarith [ha'.2 j])
      · have h2 : ∑ i, a'' i j = ∑ i, A p w i j := by
          simp only [ha'', if_neg hs]
        rw [h2, sub_self, mul_zero]
    have hvalsame : ∀ k, val (p k).1 (a'' k) = val (p k).1 (a' k) := by
      intro k
      unfold val
      apply Finset.sum_congr rfl
      intro j _
      simp only [ha'']
      split_ifs with hs
      · rfl
      · have : (p k).1 j = 0 := by
          have hn : ¬ 0 < (p k).1 j := fun h => hs ⟨k, h⟩
          exact le_antisymm (not_lt.1 hn) (p_nonneg p k j)
        rw [this, zero_mul, zero_mul]
    have hvdb : ∀ k, val (p k).1 (db k) = w.total * (val (p k).1 (a' k) - val (p k).1 (A p w k))
        + (if k = i1 then val (p k).1 c else 0) := by
      intro k
      simp only [hdb]
      rw [val_add, val_mul]
      have : val (p k).1 (fun j => a'' k j - A p w k j)
          = val (p k).1 (a'' k) - val (p k).1 (A p w k) := by
        unfold val; rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [this, hvalsame]
      congr 1
      unfold val
      split_ifs <;> simp
    apply hSB p w
    refine ⟨db, fun j => ?_, fun i j => ?_, fun k => ?_, i1, ?_⟩
    · simp only [hdb, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        hc, ← Finset.mul_sum, Finset.sum_sub_distrib]
      ring
    · simp only [hdb]
      rw [hAB]
      have h1 : 0 ≤ a'' i j := by
        simp only [ha'']; split_ifs
        · exact ha'.1 i j
        · exact (hA p w).1 i j
      have h2 : 0 ≤ (if i = i1 then c j else 0) := by
        split_ifs
        · exact hc0 j
        · exact le_rfl
      nlinarith
    · rw [hvdb]
      have h1 := mul_nonneg hW.le (sub_nonneg.2 (hno k))
      have h2 : 0 ≤ (if k = i1 then val (p k).1 c else 0) := by
        split_ifs
        · exact val_nonneg _ _ (p_nonneg p k) hc0
        · exact le_rfl
      linarith
    · rw [hvdb, if_pos rfl]
      have h1 := mul_pos hW (sub_pos.2 hi1)
      have h2 := val_nonneg _ _ (p_nonneg p i1) hc0
      linarith
