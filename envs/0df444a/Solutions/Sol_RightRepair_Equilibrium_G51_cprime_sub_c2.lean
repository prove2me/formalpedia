-- Prove2me | solution 1 for RightRepair.Equilibrium.G51_cprime_sub_c2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-16T08:27:29.865349+00:00
-- url     : https://prove2.me/submissions/e544a2d7-9e34-4f1f-8569-f0fa317554b8

import Mathlib
import Definitions.Def_RightRepair_Equilibrium_Setting
open RightRepair.Equilibrium

theorem solution(P : Params) (hP : Standing P) :
    cPrimeLow P - c2 P =
      (2 - P.f) * (P.cM - (2 * P.cI - P.δ)) ∧
    (P.cI < (P.δ + P.cM) / 2 → 0 < cPrimeLow P - c2 P) := by
  have hd : P.δ ≠ 0 := hP.δ_pos.ne'
  have hf : 2 - P.f ≠ 0 := by linarith [hP.f_lt_one]
  have key : cPrimeLow P - c2 P = (2 - P.f) * (P.cM - (2 * P.cI - P.δ)) := by
    unfold cPrimeLow c2
    field_simp
    ring
  refine ⟨key, fun h => ?_⟩
  rw [key]
  apply mul_pos <;> linarith [hP.f_lt_one]
