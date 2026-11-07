-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_tensorCode_lift_punctured
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:05:01.364549+00:00
-- url     : https://prove2.me/submissions/8290fa53-8eaf-46a6-b00f-1717f41d2d3f

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
import Theorems.Thm_QEC_Coding_QuantumTanner_pureWord_mem_tensorCode
import Theorems.Thm_QEC_Coding_QuantumTanner_tensorCode_induction


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (CA : LinearCode F A) (CB : LinearCode F B)
    (removedA : Finset A) (removedB : Finset B)
    (x : Word F (KeptCoordinate removedA × KeptCoordinate removedB))
    (hx : x ∈
      (tensorCode (puncturedCode CA removedA) (puncturedCode CB removedB)).carrier) :
    ∃ z : Word F (A × B), z ∈ (tensorCode CA CB).carrier ∧
      tensorPunctureMap removedA removedB z = x := by
  apply tensorCode_induction (puncturedCode CA removedA) (puncturedCode CB removedB)
    ?_ ?_ ?_ x hx
  · exact ⟨0, (tensorCode CA CB).carrier.zero_mem, map_zero _⟩
  · intro y z hy hz
    obtain ⟨Y, hY, hYeq⟩ := hy
    obtain ⟨Z, hZ, hZeq⟩ := hz
    exact ⟨Y + Z, (tensorCode CA CB).carrier.add_mem hY hZ,
      by rw [map_add, hYeq, hZeq]⟩
  · intro a ha b hb
    obtain ⟨aFull, haFull, haEq⟩ := (mem_puncturedCode CA removedA a).mp ha
    obtain ⟨bFull, hbFull, hbEq⟩ := (mem_puncturedCode CB removedB b).mp hb
    refine ⟨(fun ab => aFull ab.1 * bFull ab.2),
      pureWord_mem_tensorCode CA CB aFull bFull haFull hbFull, ?_⟩
    ext ab
    exact congrArg₂ (· * ·) (congrFun haEq ab.1) (congrFun hbEq ab.2)
end QEC.Coding.QuantumTanner
