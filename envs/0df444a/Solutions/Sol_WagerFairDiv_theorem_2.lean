-- Prove2me | solution 1 for WagerFairDiv.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:52:26.39239+00:00
-- url     : https://prove2.me/submissions/e5469d8d-97b3-4f7e-bfd2-eba9f40886c7

import Mathlib
import Definitions.Def_WagerFairDiv_Model
import Definitions.Def_WagerFairDiv_AllocationProperties
import Definitions.Def_WagerFairDiv_WageringProperties
import Definitions.Def_WagerFairDiv_CorrespondingMechanisms

open WagerFairDiv in
theorem solution {n m : ℕ} (A B : Mech n m) (hAB : Corresponding A B) (hIC : AllocWeakIC A) :
    Proportional A ↔ IndivRational B := by
  have hB : ∀ p w i, B p w i = fun j => w.total * A p w i j := fun p w i => funext (hAB p w i)
  have hval : ∀ (x : Fin m → ℝ) (c : ℝ) (y : Fin m → ℝ),
      WagerFairDiv.val x (fun j => c * y j) = c * WagerFairDiv.val x y := by
    intro x c y
    unfold WagerFairDiv.val
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have htot : ∀ (w : PosVec n) (i : Fin n), 0 < w.total := by
    intro w i
    have h1 : w.1 i ≤ ∑ j, w.1 j :=
      Finset.single_le_sum (fun j _ => (w.2 j).le) (Finset.mem_univ i)
    unfold PosVec.total
    linarith [w.2 i]
  constructor
  · intro hP i π
    refine ⟨π, fun p w => ?_⟩
    have h := hP (Function.update p i π) w i
    rw [Function.update_self] at h
    rw [div_le_iff₀ (htot w i)] at h
    rw [hB, hval]
    linarith [mul_comm (WagerFairDiv.val π.1 (A (Function.update p i π) w i)) w.total]
  · intro hIR v e i
    obtain ⟨r, hr⟩ := hIR i (v i)
    have h1 := hr v e
    have h2 := hIC i (v i) (Function.update v i r) e
    rw [Function.update_idem, Function.update_eq_self] at h2
    rw [hB, hval] at h1
    rw [div_le_iff₀ (htot e i)]
    nlinarith [htot e i]
