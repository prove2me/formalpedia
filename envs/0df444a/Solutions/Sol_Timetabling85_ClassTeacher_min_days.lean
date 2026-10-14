-- Prove2me | solution 1 for Timetabling85.ClassTeacher.min_days
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-13T10:45:53.795106+00:00
-- url     : https://prove2.me/submissions/678bdbcd-4c28-4444-9032-83da667299a7

import Mathlib
import Definitions.Def_Timetabling85_ClassTeacher_Problems
import Theorems.Thm_Timetabling85_ClassTeacher_prop_2_2

namespace Timetabling85.ClassTeacher

theorem hi_le_iff_mul_le {s b p : ℕ} (hb : 0 < b) :
    hi s b ≤ p ↔ s ≤ p * b := by
  unfold hi
  rw [Nat.ceil_le]
  have hbq : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
  rw [div_le_iff₀ hbq]
  norm_cast

end Timetabling85.ClassTeacher

theorem solution {m n : ℕ} (R : Fin m → Fin n → ℕ)
    (a : Fin m → ℕ) (b : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (p : ℕ) :
    (∃ x : Fin m → Fin n → Fin p → ℕ,
      Timetabling85.ClassTeacher.IsCT2 R p a b x) ↔
      Timetabling85.ClassTeacher.minDays R a b ≤ p := by
  constructor
  · rintro ⟨x, hx⟩
    have hbounds := (Timetabling85.ClassTeacher.prop_2_2 R p a b ha hb).1 ⟨x, hx⟩
    rcases hbounds with ⟨hcol, hrow⟩
    have hcolCeil : ∀ j, Timetabling85.ClassTeacher.hi
        (Timetabling85.ClassTeacher.colSum R j) (b j) ≤ p := by
      intro j
      exact (Timetabling85.ClassTeacher.hi_le_iff_mul_le (hb j)).2 (hcol j)
    have hrowCeil : ∀ i, Timetabling85.ClassTeacher.hi
        (Timetabling85.ClassTeacher.rowSum R i) (a i) ≤ p := by
      intro i
      exact (Timetabling85.ClassTeacher.hi_le_iff_mul_le (ha i)).2 (hrow i)
    unfold Timetabling85.ClassTeacher.minDays
    apply max_le_iff.mpr
    constructor
    · apply Finset.sup_le
      intro j hj
      exact hcolCeil j
    · apply Finset.sup_le
      intro i hi
      exact hrowCeil i
  · intro hmin
    have hmax :
        Finset.univ.sup (fun j => Timetabling85.ClassTeacher.hi
          (Timetabling85.ClassTeacher.colSum R j) (b j)) ≤ p ∧
        Finset.univ.sup (fun i => Timetabling85.ClassTeacher.hi
          (Timetabling85.ClassTeacher.rowSum R i) (a i)) ≤ p := by
      apply max_le_iff.mp
      simpa [Timetabling85.ClassTeacher.minDays] using hmin
    have hcol : ∀ j, Timetabling85.ClassTeacher.colSum R j ≤ p * b j := by
      intro j
      apply (Timetabling85.ClassTeacher.hi_le_iff_mul_le (hb j)).1
      exact (Finset.sup_le_iff.mp hmax.1) j (Finset.mem_univ j)
    have hrow : ∀ i, Timetabling85.ClassTeacher.rowSum R i ≤ p * a i := by
      intro i
      apply (Timetabling85.ClassTeacher.hi_le_iff_mul_le (ha i)).1
      exact (Finset.sup_le_iff.mp hmax.2) i (Finset.mem_univ i)
    exact (Timetabling85.ClassTeacher.prop_2_2 R p a b ha hb).2 ⟨hcol, hrow⟩

#print axioms solution
