-- Prove2me | solution 1 for Rudin.lowerSum_stable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T00:27:10.826533+00:00
-- url     : https://prove2.me/submissions/e136f827-fae1-4a02-bac7-9e5d156a237c

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_sInf_image_stable
import Theorems.Thm_Rudin_Partition_point_mem

open Rudin

theorem solution {a b : ℝ} (hab : a ≤ b) (α f g : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ ε)
    (P : Partition a b) :
    |lowerSum f α P - lowerSum g α P| ≤ ε * (α b - α a) := by
  have hinc : ∀ i < P.n, 0 ≤ α (P.x (i + 1)) - α (P.x i) := by
    intro i hi
    exact sub_nonneg.mpr (hα (P.point_mem (Nat.le_of_lt hi))
      (P.point_mem (Nat.succ_le_iff.mpr hi)) (P.mono i hi))
  have hext : ∀ i < P.n,
      |sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) -
        sInf (g '' Set.Icc (P.x i) (P.x (i + 1)))| ≤ ε := by
    intro i hi
    apply Rudin.sInf_image_stable _
      (show (Set.Icc (P.x i) (P.x (i + 1))).Nonempty from
        ⟨P.x i, le_rfl, P.mono i hi⟩) f g hε
    intro x hx
    apply hfg x
    constructor
    · exact (P.point_mem (Nat.le_of_lt hi)).1.trans hx.1
    · exact hx.2.trans (P.point_mem (Nat.succ_le_iff.mpr hi)).2
  rw [lowerSum, lowerSum, ← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ Finset.range P.n,
        (sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) *
            (α (P.x (i + 1)) - α (P.x i)) -
          sInf (g '' Set.Icc (P.x i) (P.x (i + 1))) *
            (α (P.x (i + 1)) - α (P.x i)))| ≤
        ∑ i ∈ Finset.range P.n,
          |sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) *
              (α (P.x (i + 1)) - α (P.x i)) -
            sInf (g '' Set.Icc (P.x i) (P.x (i + 1))) *
              (α (P.x (i + 1)) - α (P.x i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range P.n,
        ε * (α (P.x (i + 1)) - α (P.x i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i < P.n := Finset.mem_range.mp hi
      rw [← sub_mul, abs_mul, abs_of_nonneg (hinc i hin)]
      exact mul_le_mul_of_nonneg_right (hext i hin) (hinc i hin)
    _ = ε * (α b - α a) := by
      rw [← Finset.mul_sum]
      simpa only [P.last, P.first] using
        congrArg (fun z : ℝ => ε * z)
          (Finset.sum_range_sub (fun i => α (P.x i)) P.n)
