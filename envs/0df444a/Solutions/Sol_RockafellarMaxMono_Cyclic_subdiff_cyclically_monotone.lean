-- Prove2me | solution 1 for RockafellarMaxMono.Cyclic.subdiff_cyclically_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:25:42.862419+00:00
-- url     : https://prove2.me/submissions/ef1a20f8-ab15-44c5-a876-8fe4b41f06c2

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Cyclic_CyclicallyMonotone

set_option autoImplicit false

namespace RockafellarMaxMono.Cyclic

theorem b3bc958f_real_of_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (hf : Shared.ProperConvex f) (x : E) (x' : StrongDual ℝ E)
    (hx : x' ∈ Shared.subdiff f x) : ((f x).toReal : EReal) = f x := by
  obtain ⟨hbot, ⟨z, hz⟩, -⟩ := hf
  have htop : f x ≠ ⊤ := by
    intro h
    have := hx z
    rw [h, EReal.top_add_coe] at this
    exact hz (top_le_iff.mp this)
  exact EReal.coe_toReal htop (hbot x)

end RockafellarMaxMono.Cyclic

open RockafellarMaxMono.Cyclic RockafellarMaxMono in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (hsc : LowerSemicontinuous f) :
    IsCyclicallyMonotone (fun x => Shared.subdiff f x) := by
  intro n x x' hx
  set a : Fin (n + 1) → ℝ := fun i => (f (x i)).toReal with ha
  have hreal : ∀ i, ((a i : ℝ) : EReal) = f (x i) := fun i =>
    b3bc958f_real_of_mem f hf (x i) (x' i) (hx i)
  have key : ∀ i, a i - a (i + 1) ≤ x' i (x i - x (i + 1)) := by
    intro i
    have h := hx i (x (i + 1))
    rw [← hreal i, ← hreal (i + 1), ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    have : x' i (x i - x (i + 1)) = - x' i (x (i + 1) - x i) := by
      rw [← map_neg, neg_sub]
    rw [this]
    linarith
  have hsum : ∑ i, (a i - a (i + 1)) = 0 := by
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact (Fintype.sum_equiv (Equiv.addRight (1 : Fin (n + 1))) _ _ (fun _ => rfl)).symm
  calc (0 : ℝ) = ∑ i, (a i - a (i + 1)) := hsum.symm
    _ ≤ ∑ i, x' i (x i - x (i + 1)) := Finset.sum_le_sum (fun i _ => key i)
