-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.columnContraction_mem_of_mem_dualTensorCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:22:07.967312+00:00
-- url     : https://prove2.me/submissions/12b95522-1ed8-48e8-857d-710e5c0178ac

import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Theorems.Thm_QEC_Coding_QuantumTanner_columnContraction_eq_sum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (CA : LinearCode F A) (CB : LinearCode F B) (a : Word F A)
    (ha : a ∈ CA.dual.carrier) (x : Word F (A × B))
    (hx : x ∈ (dualTensorCode CA CB).carrier) :
    columnContraction a x ∈ CB.carrier := by
  obtain ⟨c, hc, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  have hcZero : columnContraction a c = 0 := by
    ext b
    exact CA.orthogonal_of_mem_dual ha (hc b)
  rw [map_add, hcZero, zero_add, columnContraction_eq_sum]
  apply Submodule.sum_mem
  intro i _hi
  exact CB.carrier.smul_mem _ (hr i)
end QEC.Coding.QuantumTanner
