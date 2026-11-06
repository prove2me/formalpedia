-- Prove2me | solution 2 for QEC.Coding.exists_algebraicCSSMinimumDistance_of_exists_logical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:07:19.971126+00:00
-- url     : https://prove2.me/submissions/1414954c-9de5-4e99-9568-85e7886e9284

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Coding_Core_Definitions

set_option autoImplicit false
open QEC
open QEC.Coding
universe u v w x
namespace QEC.Coding
theorem _root_.solution
    {F : Type u} {ι : Type v} [Field F] [Fintype F]
    [DecidableEq F] [Fintype ι]
    (xCode zCode : LinearCode F ι)
    (hne : ∃ x : Word F ι,
      (x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
        (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)) :
    ∃ d : Nat, AlgebraicCSSMinimumDistance xCode zCode d := by
  classical
  let logicalWords : Finset (Word F ι) :=
    Finset.univ.filter fun x =>
      (x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
        (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)
  have hnonempty : logicalWords.Nonempty := by
    rcases hne with ⟨x, hx⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image logicalWords
      (fun y : Word F ι => HammingWeight y) hnonempty
  have hxLogical :
      (x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
        (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier) :=
    (Finset.mem_filter.mp hx).2
  refine ⟨HammingWeight x, x, hxLogical, rfl, ?_⟩
  intro y hy
  exact hmin y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
end QEC.Coding
