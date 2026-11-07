-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.dualTensorCode_mem_punctured_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:23:31.866171+00:00
-- url     : https://prove2.me/submissions/7eca1645-61ec-4370-a4ae-aae7950a85e8

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (x : Word (ZMod 2) (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier) :
    (fun ab : KeptCoordinate (∅ : Finset A) × KeptCoordinate (∅ : Finset B) =>
      x (ab.1.1, ab.2.1)) ∈ (dualTensorCode (puncturedCode CA ∅) (puncturedCode CB ∅)).carrier := by
  obtain ⟨c, hc, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  apply Submodule.mem_sup.mpr
  refine ⟨(fun ab => c (ab.1.1, ab.2.1)), ?_,
    (fun ab => r (ab.1.1, ab.2.1)), ?_, rfl⟩
  · intro b
    exact (mem_puncturedCode CA ∅ _).mpr ⟨columnRestriction b.1 c, hc b.1, rfl⟩
  · intro a
    exact (mem_puncturedCode CB ∅ _).mpr ⟨rowRestriction a.1 r, hr a.1, rfl⟩
end QEC.Coding.QuantumTanner
