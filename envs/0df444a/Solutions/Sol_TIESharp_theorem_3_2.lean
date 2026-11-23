-- Prove2me | solution 1 for TIESharp.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:34:22.594807+00:00
-- url     : https://prove2.me/submissions/9d038d19-cfd3-4bfc-9fff-ffb7d2ed0b1e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TIESharp_IsFeasible
import Definitions.Def_TIESharp_IsTIE
import Definitions.Def_TIESharp_IsRApprox
import Theorems.Thm_TIESharp_theorem_3_1
import Theorems.Thm_TIESharp_local_limit_star_lower_bound

set_option autoImplicit false

open MeasureTheory

theorem solution (n : ℕ) (hn : 1 ≤ n) (F : TIESharp.Family n) (R : ℝ)
    (hF : TIESharp.IsFeasible F) (hT : TIESharp.IsTIE F)
    (hR : TIESharp.IsRApprox F R) : ((n : ℝ) + 1) / 2 ≤ R := by
  by_cases hn1 : n = 1
  · subst n
    let t : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    have ht : TIESharp.Nonneg t := by intro i j; simp [t]
    have hbound := hR 1 t ht
    have hprob := (hF 1 t ht).2
    have hmake (A : Fin 1 → Fin 1) :
        MatousekLP.Scheduling.makespan (Matrix.of t) A = 1 := by
      have hA (j : Fin 1) : A j = 0 := Subsingleton.elim _ _
      simp [MatousekLP.Scheduling.makespan, MatousekLP.Scheduling.load, t, hA]
    have hopt : TIESharp.opt t = 1 := by
      simp [TIESharp.opt, hmake]
    simp_rw [hmake, mul_one] at hbound
    rw [hprob, hopt, mul_one] at hbound
    norm_num
    exact hbound
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨g, hgmeas, hg01, yStar, hymeas, hy⟩ :=
      TIESharp.theorem_3_1 n hn2 F R hF hT hR
    exact TIESharp.local_limit_star_lower_bound n hn2 R g hgmeas hg01 yStar hymeas hy
