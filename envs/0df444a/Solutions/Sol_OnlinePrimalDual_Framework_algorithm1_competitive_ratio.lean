-- Prove2me | solution 1 for OnlinePrimalDual.Framework.algorithm1_competitive_ratio
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:14:50.296817+00:00
-- url     : https://prove2.me/submissions/27276451-1b64-4f6e-9306-fc95af61861b

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg1X

namespace OnlinePrimalDual.Framework

/-- The one-variable, one-constraint instance with `c = 1`, `d = 1`. -/
def aux_a1cr_inst : CoveringInstance Unit Unit where
  S := fun _ => Finset.univ
  c := fun _ => 1
  hc_pos := fun _ => one_pos
  d := 1
  hd_pos := one_pos
  hd_bound := fun _ => by simp

lemma aux_a1cr_alg1X (i : Unit) :
    alg1X aux_a1cr_inst [()] (fun _ => 3) i = 7 := by
  simp [alg1X, aux_a1cr_inst, Function.iterate_succ, List.filter]
  norm_num

lemma aux_a1cr_logb : Real.logb 2 (3 * (1 : ℝ) + 1) = 2 := by
  rw [show (3 * (1 : ℝ) + 1) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]
  simp

end OnlinePrimalDual.Framework

open OnlinePrimalDual.Framework

theorem solution : ¬ (∀ {I J : Type} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (hc1 : ∀ i, 1 ≤ inst.c i) (ord : List J)
    (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) (t : J → ℕ)
    (h_feasible : ∀ j, 1 ≤ ∑ i ∈ inst.S j, alg1X inst ord t i),
    (∀ i : I, (∑ j ∈ Finset.univ.filter (fun j => i ∈ inst.S j), (t j : ℝ)) ≤
        inst.c i * Real.logb 2 (3 * inst.d + 1)) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * alg1X inst ord t i ≤
          2 * Real.logb 2 (3 * inst.d + 1) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * ∑ j, (t j : ℝ))) := by
  intro h
  have key := (@h Unit Unit _ _ _ _ aux_a1cr_inst (fun _ => le_refl _) [()]
    (List.nodup_singleton _) (fun j => by simp) (fun _ => 3)
    (fun j => by
      show (1:ℝ) ≤ ∑ i ∈ (Finset.univ : Finset Unit), alg1X aux_a1cr_inst [()] (fun _ => 3) i
      simp [aux_a1cr_alg1X])).1 ()
  have hl := aux_a1cr_logb
  simp only [aux_a1cr_inst] at key hl ⊢
  rw [hl] at key
  simp at key
  norm_num at key
