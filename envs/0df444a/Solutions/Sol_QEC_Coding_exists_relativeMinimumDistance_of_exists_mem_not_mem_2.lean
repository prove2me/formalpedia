-- Prove2me | solution 2 for QEC.Coding.exists_relativeMinimumDistance_of_exists_mem_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:07:25.751128+00:00
-- url     : https://prove2.me/submissions/b3a15f54-78d1-4e9c-916b-8647210c1d3e

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
namespace QEC.Coding
theorem _root_.solution
    {F : Type u} {ι : Type v} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (ambient trivial : LinearCode F ι) (_hsub : trivial.carrier ≤ ambient.carrier)
    (hne : ∃ x : Word F ι, x ∈ ambient.carrier ∧ x ∉ trivial.carrier) :
    ∃ d : Nat, RelativeMinimumDistance ambient trivial d := by
  classical
  let relativeCodewords : Finset (Word F ι) :=
    Finset.univ.filter fun x => x ∈ ambient.carrier ∧ x ∉ trivial.carrier
  have hnonempty : relativeCodewords.Nonempty := by
    rcases hne with ⟨x, hxAmbient, hxTrivial⟩
    exact ⟨x, by simp [relativeCodewords, hxAmbient, hxTrivial]⟩
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image relativeCodewords (fun y : Word F ι => HammingWeight y) hnonempty
  have hxAmbient : x ∈ ambient.carrier := by
    exact (Finset.mem_filter.mp hx).2.1
  have hxTrivial : x ∉ trivial.carrier := by
    exact (Finset.mem_filter.mp hx).2.2
  refine ⟨HammingWeight x, x, hxAmbient, hxTrivial, rfl, ?_⟩
  intro y hyAmbient hyTrivial
  exact hmin y (by simp [relativeCodewords, hyAmbient, hyTrivial])
end QEC.Coding
