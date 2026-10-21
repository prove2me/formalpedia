-- Prove2me | solution 1 for SelfReplic.Strong.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:25:27.149318+00:00
-- url     : https://prove2.me/submissions/c48d10f8-71b2-42ce-9f6e-5fccb520d931
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SelfReplic_Strong_theorem_1_a
import Theorems.Thm_SelfReplic_Strong_theorem_1_b
import Theorems.Thm_SelfReplic_Strong_theorem_1_c

open SelfReplic.Strong

theorem solution (P : Params) (hP : P.Standing) (hSR : P.StrongRepl)
    (Ilow Ihigh : ℝ) (hlow : IsLowLevel P Ilow) (hhigh : IsHighLevel P Ihigh) :
    (P.IL < Ilow → ∃ ts ∈ Set.Icc 0 P.T, ∃ x : Traj,
        IsOptimal P x ∧ ProdAlwaysOn P x ∧ SalesOnFrom P x ts ∧ DepletedExactlyAtT P x) ∧
    (Ilow < P.IL → P.IL < Ihigh → ∃ tp ∈ Set.Icc 0 P.T, ∃ x : Traj,
        IsOptimal P x ∧ SalesAlwaysOn P x ∧ ProdOnFrom P x tp ∧ DepletedExactlyAtT P x) ∧
    (Ihigh < P.IL → ∃ x : Traj,
        IsOptimal P x ∧ SalesAlwaysOn P x ∧ ProdAlwaysOff P x ∧ 0 < x.I P.T) :=
  ⟨theorem_1_a P hP hSR Ilow Ihigh hlow hhigh, theorem_1_b P hP hSR Ilow Ihigh hlow hhigh,
    theorem_1_c P hP hSR Ilow Ihigh hlow hhigh⟩
