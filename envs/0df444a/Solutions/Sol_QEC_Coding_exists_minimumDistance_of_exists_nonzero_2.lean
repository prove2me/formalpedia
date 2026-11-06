-- Prove2me | solution 2 for QEC.Coding.exists_minimumDistance_of_exists_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:07:22.211214+00:00
-- url     : https://prove2.me/submissions/15a60786-cdf3-4bc7-9b28-96f4602f79a1

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
theorem _root_.solution {F : Type u} {ι : Type v}
    [Field F] [Fintype F] [DecidableEq F] [Fintype ι] (C : LinearCode F ι)
    (hC : ∃ x : Word F ι, x ∈ C.carrier ∧ x ≠ 0) :
    ∃ d : Nat, MinimumDistance C d := by
  classical
  let nonzeroCodewords : Finset (Word F ι) :=
    Finset.univ.filter fun x => x ∈ C.carrier ∧ x ≠ 0
  have hnonempty : nonzeroCodewords.Nonempty := by
    rcases hC with ⟨x, hxC, hx0⟩
    exact ⟨x, by simp [nonzeroCodewords, hxC, hx0]⟩
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image nonzeroCodewords (fun y : Word F ι => HammingWeight y) hnonempty
  have hxC : x ∈ C.carrier := by
    exact (Finset.mem_filter.mp hx).2.1
  have hx0 : x ≠ 0 := by
    exact (Finset.mem_filter.mp hx).2.2
  refine ⟨HammingWeight x, x, hxC, hx0, rfl, ?_⟩
  intro y hyC hy0
  exact hmin y (by simp [nonzeroCodewords, hyC, hy0])
end QEC.Coding
