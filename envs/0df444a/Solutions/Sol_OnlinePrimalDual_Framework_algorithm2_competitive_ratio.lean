-- Prove2me | solution 1 for OnlinePrimalDual.Framework.algorithm2_competitive_ratio
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:18:45.817574+00:00
-- url     : https://prove2.me/submissions/ab700299-a9ae-4188-b70f-f7dae3966a5d

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg2X

namespace OnlinePrimalDual.Framework

/-- The one-element, one-constraint instance with unit cost and `d = 1`. -/
def aux_a2cr_inst : CoveringInstance Unit Unit where
  S := fun _ => Finset.univ
  c := fun _ => 1
  hc_pos := fun _ => one_pos
  d := 1
  hd_pos := one_pos
  hd_bound := fun _ => by simp

lemma aux_a2cr_dualSum : dualSum aux_a2cr_inst (fun _ => 2) () = 2 := by
  simp [dualSum, aux_a2cr_inst]

lemma aux_a2cr_alg2X : alg2X aux_a2cr_inst (fun _ => 2) () = 3 := by
  unfold alg2X
  rw [aux_a2cr_dualSum]
  have h1 : aux_a2cr_inst.d = 1 := rfl
  have h2 : aux_a2cr_inst.c () = 1 := rfl
  rw [h1, h2]
  have h3 : Real.log (1 + 1) / 1 * 2 = Real.log 4 := by
    rw [div_one, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    ring
  rw [h3, Real.exp_log (by norm_num)]
  norm_num

end OnlinePrimalDual.Framework

open OnlinePrimalDual.Framework

theorem solution : ¬ (∀ {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : CoveringInstance I J) (y : J → ℝ) (hy_nonneg : ∀ j, 0 ≤ y j)
    (h_feasible : ∀ j, 1 ≤ ∑ i ∈ inst.S j, alg2X inst y i),
    (∀ i : I, dualSum inst y i ≤ inst.c i) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * alg2X inst y i ≤
          2 * Real.log (1 + inst.d) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * Real.log (1 + inst.d) * ∑ j, y j)) := by
  intro h
  have hfeas : ∀ j, 1 ≤ ∑ i ∈ aux_a2cr_inst.S j, alg2X aux_a2cr_inst (fun _ => (2 : ℝ)) i := by
    intro j
    have hS : aux_a2cr_inst.S j = Finset.univ := rfl
    rw [hS, Fintype.sum_unique]
    have : (default : Unit) = () := rfl
    rw [this, aux_a2cr_alg2X]
    norm_num
  have h1 := (h aux_a2cr_inst (fun _ => (2 : ℝ)) (fun _ => by norm_num) hfeas).1 ()
  rw [aux_a2cr_dualSum] at h1
  have h2 : aux_a2cr_inst.c () = 1 := rfl
  rw [h2] at h1
  norm_num at h1
