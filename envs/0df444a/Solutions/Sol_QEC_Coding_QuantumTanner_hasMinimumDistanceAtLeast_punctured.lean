-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.hasMinimumDistanceAtLeast_punctured
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:50:22.580875+00:00
-- url     : https://prove2.me/submissions/b90d145e-5329-4288-9302-9e14a96cb624

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Theorems.Thm_QEC_Coding_QuantumTanner_hammingWeight_puncture_loss_le

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution [DecidableEq F]
    (C : LinearCode F A) (d : Nat) (hC : HasMinimumDistanceAtLeast C d)
    (removed : Finset A) :
    HasMinimumDistanceAtLeast (puncturedCode C removed) (d - removed.card) := by
  intro y hy hy0
  obtain ⟨x, hx, rfl⟩ := (mem_puncturedCode C removed y).mp hy
  have hx0 : x ≠ 0 := by
    intro h
    exact hy0 (by rw [h, map_zero])
  have hDistance := hC x hx hx0
  have hLoss := hammingWeight_puncture_loss_le removed x
  omega
end QEC.Coding.QuantumTanner
