-- Prove2me | solution 1 for QuantumSixJ.recurrences
-- status  : ACCEPTED   (prove)
-- author  : @igor.kh
-- created : 2026-11-13T09:14:58.678099+00:00
-- url     : https://prove2.me/submissions/7eac94fb-3c25-4fdd-8797-fbb30e7ff73e

import Theorems.Thm_QuantumSixJ_sum_recurrence
import Theorems.Thm_QuantumSixJ_network_recurrence

universe v u

theorem solution : QuantumSixJ.SumRecurrence ∧ QuantumSixJ.NetworkRecurrence.{v,u} := by
  exact ⟨QuantumSixJ.sum_recurrence, QuantumSixJ.network_recurrence⟩
