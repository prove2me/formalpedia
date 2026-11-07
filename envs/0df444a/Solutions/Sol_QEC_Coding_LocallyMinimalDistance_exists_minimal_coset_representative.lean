-- Prove2me | solution 1 for QEC.Coding.LocallyMinimalDistance.exists_minimal_coset_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:43.63901+00:00
-- url     : https://prove2.me/submissions/5cd7fa1f-dcee-4214-9b24-dd36384f9be4

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]
namespace QEC.Coding.LocallyMinimalDistance
theorem _root_.solution
    (weight : C → Nat) (B : AddSubgroup C) (c : C) :
    ∃ b ∈ B, weight (c + b) = cosetWeight weight B c := by
  have hnonempty : {n : Nat | ∃ b ∈ B, weight (c + b) = n}.Nonempty := by
    refine ⟨weight (c + 0), ?_⟩
    exact ⟨0, B.zero_mem, rfl⟩
  exact Nat.sInf_mem hnonempty
end QEC.Coding.LocallyMinimalDistance
