-- Prove2me | solution 1 for ZipkinLostSales.Bounds.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:47:40.596749+00:00
-- url     : https://prove2.me/submissions/c4acd887-7bb4-4bb9-8fcf-f639a0434a01

import Mathlib
import Definitions.Def_ZipkinLostSales_Bounds_Model

open ZipkinLostSales.Bounds ZipkinLostSales.LNatural

private def running (v d : ℕ → ℝ) : ℕ → ℝ
  | 0 => v 0
  | j + 1 => max (running v d j - d j) (v (j + 1))

private theorem running_le (v d : ℕ → ℝ) (j : ℕ) (r : ℝ) :
    running v d j ≤ r ↔ ∀ l ≤ j, v l - ∑ k ∈ Finset.Ico l j, d k ≤ r := by
  induction j generalizing r with
  | zero => simp [running]
  | succ j ih =>
    rw [running, max_le_iff]
    constructor
    · rintro ⟨hprev, hj⟩ l hl
      by_cases he : l = j + 1
      · subst l; simpa using hj
      · have hlj : l ≤ j := by omega
        have hh := (ih (r + d j)).mp (by linarith) l hlj
        rw [Finset.sum_Ico_succ_top hlj]
        linarith
    · intro h
      constructor
      · have hh : running v d j ≤ r + d j := (ih _).mpr (by
          intro l hl
          have hh := h l (by omega)
          rw [Finset.sum_Ico_succ_top hl] at hh
          linarith)
        linarith
      · simpa using h (j + 1) (le_refl _)

private theorem running_onHand {L : ℕ} (hL : 0 < L) (v D : Fin L → ℝ) (z : ℝ) :
    ∀ j < L, running (vext v) (vext D) j = onHand v z D j + vext v (j + 1) := by
  intro j hj
  induction j with
  | zero => simp [running, onHand, arrival, xext, hL]
  | succ j ih =>
    have hj' : j < L := by omega
    rw [running, ih hj', onHand, arrival, if_pos hj, xext]
    have hm : max (onHand v z D j + vext v (j + 1) - vext D j) (vext v (j + 1)) =
        max (onHand v z D j - vext D j) 0 + vext v (j + 1) := by
      convert max_add_add_right (onHand v z D j - vext D j) 0 (vext v (j + 1)) using 1 <;> ring
    rw [hm]
    ring

theorem solution {L : ℕ} (hL : 0 < L) (v : Fin L → ℝ) (z : ℝ) (D : Fin L → ℝ) :
    yPlusL v z D =
      z + max ((Finset.univ : Finset (Fin L)).sup' ⟨⟨0, hL⟩, Finset.mem_univ _⟩
        (fun l => v l - ∑ j ∈ Finset.Ici l, D j)) 0 := by
  let s := (Finset.univ : Finset (Fin L)).sup' ⟨⟨0, hL⟩, Finset.mem_univ _⟩
        (fun l => v l - ∑ j ∈ Finset.Ici l, D j)
  have hsum (l : Fin L) : ∑ k ∈ Finset.Ico l.val L, vext D k = ∑ j ∈ Finset.Ici l, D j := by
    apply Finset.sum_bij (fun k hk => (⟨k, (Finset.mem_Ico.mp hk).2⟩ : Fin L))
    · intro k hk
      exact Finset.mem_Ici.mpr (Fin.le_iff_val_le_val.mpr (Finset.mem_Ico.mp hk).1)
    · intro k hk k' hk' he; exact congrArg Fin.val he
    · intro j hj
      refine ⟨j.val, ?_, rfl⟩
      exact Finset.mem_Ico.mpr ⟨by simpa using hj, j.isLt⟩
    · intro k hk; simp [vext, (Finset.mem_Ico.mp hk).2]
  have hchar (r : ℝ) : running (vext v) (vext D) L ≤ r ↔ max s 0 ≤ r := by
    rw [running_le, max_le_iff]
    constructor
    · intro hh
      constructor
      · apply Finset.sup'_le
        intro l hl
        have hh' := hh l.val l.isLt.le
        rw [hsum l] at hh'
        simpa [vext, l.isLt] using hh'
      · simpa [vext] using hh L (le_refl _)
    · rintro ⟨hs, hr⟩ l hl
      by_cases hlt : l < L
      · have hh := (Finset.le_sup' (fun l : Fin L => v l - ∑ j ∈ Finset.Ici l, D j)
            (Finset.mem_univ (⟨l, hlt⟩ : Fin L))).trans hs
        simpa [vext, hlt, ← hsum ⟨l, hlt⟩] using hh
      · have he : l = L := by omega
        subst l; simpa [vext] using hr
  have he : running (vext v) (vext D) L = max s 0 :=
    le_antisymm ((hchar _).mpr le_rfl) ((hchar _).mp le_rfl)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  have hv : vext v (j + 1) = 0 := by simp [vext]
  have hh := running_onHand hL v D z j (by omega)
  simp only [running, hv, add_zero] at he hh
  simp only [yPlusL, onHand, arrival, lt_self_iff_false, if_false]
  rw [← hh, he]
  exact add_comm _ _

#print axioms solution
