-- Prove2me | solution 1 for QFlexSC.ZeroInv.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @EvanLLL
-- created : 2026-10-08T03:30:54.916017+00:00
-- url     : https://prove2.me/submissions/1610cd70-959d-4425-8abc-53db8fc2afb7

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model

open QFlexSC.ZeroInv

theorem solution (P : QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ)
    (hstd : ∀ q, 1 ≤ q → 0 ≤ P.αin q ∧ 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1 ∧
      0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (hf : ∀ t j, 0 ≤ f t j)
    (ha : IROut P f)
    (hc : I₀ = 0)
    (hr₀ : r₀ = f 0)
    (hd : ∀ j, 1 ≤ j → Acum P.αout j ≤ Acum P.αin j ∧ Ωcum P.ωout j ≤ Ωcum P.ωin j) :
    (∀ t : ℕ, inv P I₀ r₀ f t = 0) ∧
      ((∀ j, 1 ≤ j → Acum P.αin j = Acum P.αout j ∧ Ωcum P.ωin j = Ωcum P.ωout j) →
        (∀ q, 1 ≤ q → P.ωin q < 1) →
        ∀ t : ℕ, 1 ≤ t → ∀ j : ℕ, sched P I₀ r₀ f t j = f t j) := by
  classical
  let Ain (j : ℕ) : ℝ := 1 + Acum P.αin j
  let Aout (j : ℕ) : ℝ := 1 + Acum P.αout j
  let Bin (j : ℕ) : ℝ := 1 - Ωcum P.ωin j
  let Bout (j : ℕ) : ℝ := 1 - Ωcum P.ωout j
  have hA (a : ℕ → ℝ) (ha' : ∀ q, 1 ≤ q → 0 ≤ a q) (j : ℕ) :
      1 ≤ 1 + Acum a j := by
    have hp : (1 : ℝ) ≤ ∏ q ∈ Finset.Icc 1 j, (1 + a q) := by
      apply Finset.one_le_prod
      intro q hq
      have := ha' q (Finset.mem_Icc.mp hq).1
      linarith
    dsimp [Acum]
    linarith
  have hAi (j : ℕ) : 0 < Ain j :=
    lt_of_lt_of_le zero_lt_one (hA P.αin (fun q hq => (hstd q hq).1) j)
  have hAo (j : ℕ) : 1 ≤ Aout j :=
    hA P.αout (fun q hq => (hstd q hq).2.1) j
  have hBi (j : ℕ) : 0 ≤ Bin j := by
    simpa [Bin, Ωcum] using
      (Finset.prod_nonneg (s := Finset.Icc 1 j) (f := fun q => 1 - P.ωin q)
        (fun q hq => sub_nonneg.mpr (hstd q (Finset.mem_Icc.mp hq).1).2.2.2.1))
  have hBo (j : ℕ) : 0 ≤ Bout j ∧ Bout j ≤ 1 := by
    have hnonneg : ∀ q ∈ Finset.Icc 1 j, 0 ≤ 1 - P.ωout q :=
      fun q hq => sub_nonneg.mpr (hstd q (Finset.mem_Icc.mp hq).1).2.2.2.2.2
    have hle : ∀ q ∈ Finset.Icc 1 j, 1 - P.ωout q ≤ 1 := by
      intro q hq
      have := (hstd q (Finset.mem_Icc.mp hq).1).2.2.2.2.1
      linarith
    simpa [Bout, Ωcum] using
      And.intro (Finset.prod_nonneg hnonneg) (Finset.prod_le_one hnonneg hle)
  have hAdom (j : ℕ) : Aout j ≤ Ain j := by
    by_cases hj : j = 0
    · subst j
      simp [Aout, Ain, Acum]
    · have := (hd j (by omega)).1
      dsimp [Aout, Ain]
      linarith
  have hBdom (j : ℕ) : Bin j ≤ Bout j := by
    by_cases hj : j = 0
    · subst j
      simp [Bin, Bout, Ωcum]
    · have := (hd j (by omega)).2
      dsimp [Bin, Bout]
      linarith
  have hBsucc (w : ℕ → ℝ) (j : ℕ) :
      1 - Ωcum w (j + 1) = (1 - Ωcum w j) * (1 - w (j + 1)) := by
    simpa [Ωcum] using
      (Finset.prod_Icc_succ_top (show 1 ≤ j + 1 by omega) (fun q => 1 - w q))
  -- The weighted schedule bound is stable under one MC entry.
  have hentry (t : ℕ)
      (hprev : ∀ j, Bin j * sched P I₀ r₀ f t j ≤ Bout j * f t j) (j : ℕ) :
      Bin j * entry P (sched P I₀ r₀ f t) (f (t + 1)) 0 j ≤
        Bout j * f (t + 1) j := by
    have htarget : target P (f (t + 1)) 0 j ≤ f (t + 1) j := by
      change (Aout j * f (t + 1) j - 0) / Ain j ≤ f (t + 1) j
      apply (div_le_iff₀ (hAi j)).2
      have := mul_le_mul_of_nonneg_right (hAdom j) (hf (t + 1) j)
      nlinarith
    have ht : Bin j * target P (f (t + 1)) 0 j ≤ Bout j * f (t + 1) j :=
      (mul_le_mul_of_nonneg_left htarget (hBi j)).trans
        (mul_le_mul_of_nonneg_right (hBdom j) (hf (t + 1) j))
    have hl :
        Bin j * ((1 - P.ωin (j + 1)) * sched P I₀ r₀ f t (j + 1)) ≤
          Bout j * f (t + 1) j := by
      calc
        _ = Bin (j + 1) * sched P I₀ r₀ f t (j + 1) := by
          dsimp [Bin]
          rw [hBsucc]
          ring
        _ ≤ Bout (j + 1) * f t (j + 1) := hprev (j + 1)
        _ = Bout j * ((1 - P.ωout (j + 1)) * f t (j + 1)) := by
          dsimp [Bout]
          rw [hBsucc]
          ring
        _ ≤ Bout j * f (t + 1) j :=
          mul_le_mul_of_nonneg_left (ha t j).1 (hBo j).1
    unfold entry
    rcases le_total (target P (f (t + 1)) 0 j)
      ((1 - P.ωin (j + 1)) * sched P I₀ r₀ f t (j + 1)) with h | h
    · rw [max_eq_right h]
      exact hl
    · rw [max_eq_left h]
      exact ht
  -- No projected stock accumulates when the preceding weighted bound holds.
  have hproj (t : ℕ)
      (hprev : ∀ j, Bin j * sched P I₀ r₀ f t j ≤ Bout j * f t j) :
      ∀ j, proj P 0 (sched P I₀ r₀ f t) (f (t + 1)) j = 0 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [proj, ih, zero_add]
      apply max_eq_left
      change Bin j * entry P (sched P I₀ r₀ f t) (f (t + 1)) 0 j -
        Aout j * f (t + 1) j ≤ 0
      exact sub_nonpos.mpr ((hentry t hprev j).trans
        (mul_le_mul_of_nonneg_right ((hBo j).2.trans (hAo j)) (hf (t + 1) j)))
  have hall : ∀ t, inv P I₀ r₀ f t = 0 ∧
      ∀ j, Bin j * sched P I₀ r₀ f t j ≤ Bout j * f t j := by
    intro t
    induction t with
    | zero =>
      constructor
      · simpa [inv, run] using hc
      · intro j
        change Bin j * r₀ j ≤ Bout j * f 0 j
        rw [hr₀]
        exact mul_le_mul_of_nonneg_right (hBdom j) (hf 0 j)
    | succ t ih =>
      have hs (j : ℕ) :
          sched P I₀ r₀ f (t + 1) j =
            entry P (sched P I₀ r₀ f t) (f (t + 1)) 0 j := by
        rw [sched_succ]
        change entry P (sched P I₀ r₀ f t) (f (t + 1))
          (proj P (inv P I₀ r₀ f t) (sched P I₀ r₀ f t) (f (t + 1)) j) j = _
        rw [ih.1, hproj t ih.2 j]
      have hz : entry P (sched P I₀ r₀ f t) (f (t + 1)) 0 0 = f (t + 1) 0 := by
        apply le_antisymm
        · simpa [Bin, Bout, Ωcum] using hentry t ih.2 0
        · have hzero : target P (f (t + 1)) 0 0 = f (t + 1) 0 := by
            simp [target, Acum]
          unfold entry
          rw [hzero]
          exact le_max_left _ _
      constructor
      · rw [inv_succ, ih.1, hs 0, hz]
        ring
      · intro j
        rw [hs j]
        exact hentry t ih.2 j
  refine ⟨fun t => (hall t).1, ?_⟩
  intro heq hstrict t ht j
  cases t with
  | zero => omega
  | succ t =>
    have hAeq : Aout j = Ain j := by
      by_cases hj : j = 0
      · subst j
        simp [Aout, Ain, Acum]
      · exact congrArg (fun x : ℝ => 1 + x) (heq j (by omega)).1.symm
    have hBeq : Bout j = Bin j := by
      by_cases hj : j = 0
      · subst j
        simp [Bout, Bin, Ωcum]
      · exact congrArg (fun x : ℝ => 1 - x) (heq j (by omega)).2.symm
    have hBpos : 0 < Bin j := by
      simpa [Bin, Ωcum] using
        (Finset.prod_pos (s := Finset.Icc 1 j) (f := fun q => 1 - P.ωin q)
          (fun q hq => sub_pos.mpr (hstrict q (Finset.mem_Icc.mp hq).1)))
    have hupper : sched P I₀ r₀ f (t + 1) j ≤ f (t + 1) j := by
      have hbound := (hall (t + 1)).2 j
      rw [hBeq] at hbound
      exact le_of_mul_le_mul_left hbound hBpos
    have htarget : target P (f (t + 1)) 0 j = f (t + 1) j := by
      change (Aout j * f (t + 1) j - 0) / Ain j = f (t + 1) j
      apply (div_eq_iff (ne_of_gt (hAi j))).2
      rw [hAeq]
      ring
    apply le_antisymm hupper
    rw [sched_succ]
    change f (t + 1) j ≤ entry P (sched P I₀ r₀ f t) (f (t + 1))
      (proj P (inv P I₀ r₀ f t) (sched P I₀ r₀ f t) (f (t + 1)) j) j
    rw [(hall t).1, hproj t (hall t).2 j]
    unfold entry
    rw [htarget]
    exact le_max_left _ _


#print axioms solution
