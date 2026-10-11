-- Prove2me | solution 1 for TensorNP.Rank.real_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:45:34.200335+00:00
-- url     : https://prove2.me/submissions/545121bf-2510-483f-affd-c2fe7e83c50a

import Definitions.Def_TensorNP_Rank_Defs
import Definitions.Def_TensorNP_Rank_Construction
import Mathlib

open TensorNP.Rank

theorem solution :
    let x : Fin 2 → ℝ := fun i => (vecX i : ℝ)
    let y : Fin 2 → ℝ := fun i => (vecY i : ℝ)
    let z : Fin 2 → ℝ := x + Real.sqrt 2 • y
    let zbar : Fin 2 → ℝ := x - Real.sqrt 2 • y
    (outer zbar z zbar + outer z zbar z = fun i j k => (tensorA i j k : ℝ)) ∧
      rankOver ℝ (fun i j k => (tensorA i j k : ℝ)) ≤ 2 := by
  let x : Fin 2 → ℝ := fun i => (vecX i : ℝ)
  let y : Fin 2 → ℝ := fun i => (vecY i : ℝ)
  let z : Fin 2 → ℝ := x + Real.sqrt 2 • y
  let zbar : Fin 2 → ℝ := x - Real.sqrt 2 • y
  change (outer zbar z zbar + outer z zbar z = fun i j k => (tensorA i j k : ℝ)) ∧ _
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h : outer zbar z zbar + outer z zbar z = fun i j k => (tensorA i j k : ℝ) := by
    ext i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [x, y, z, zbar, outer, tensorA, vecX, vecY] <;> nlinarith [hs]
  refine ⟨h, ?_⟩
  apply Nat.sInf_le
  refine ⟨![1, 1], ![zbar, z], ![z, zbar], ![zbar, z], ?_⟩
  simpa [Fin.sum_univ_two] using h.symm
