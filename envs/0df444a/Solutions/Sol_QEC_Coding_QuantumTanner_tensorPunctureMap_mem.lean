-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.tensorPunctureMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:41:46.412251+00:00
-- url     : https://prove2.me/submissions/a999492c-3d54-4d2d-95b2-4b036235a792

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture

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
    (x : Word F (A × B)) (hx : x ∈ (tensorCode CA CB).carrier) :
    tensorPunctureMap removedA removedB x ∈
      (tensorCode (puncturedCode CA removedA) (puncturedCode CB removedB)).carrier := by
  constructor
  · intro b
    apply (mem_puncturedCode CA removedA _).mpr
    exact ⟨columnRestriction b.1 x, hx.1 b.1, rfl⟩
  · intro a
    apply (mem_puncturedCode CB removedB _).mpr
    exact ⟨rowRestriction a.1 x, hx.2 a.1, rfl⟩
end QEC.Coding.QuantumTanner
