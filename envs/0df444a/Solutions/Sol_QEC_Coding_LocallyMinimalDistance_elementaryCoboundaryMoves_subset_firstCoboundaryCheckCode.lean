-- Prove2me | solution 1 for QEC.Coding.LocallyMinimalDistance.elementaryCoboundaryMoves_subset_firstCoboundaryCheckCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:54:15.133907+00:00
-- url     : https://prove2.me/submissions/133cea8c-781c-4b6f-bb4a-9106d0eae45a

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.Order.Lattice.Nat
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LocallyMinimalDistance
universe u v
variable {C : Type*} [AddCommGroup C]
namespace QEC.Coding.LocallyMinimalDistance
theorem _root_.solution
    {F : Type u} {ι κ₀ κ₂ : Type v} [Field F] [Fintype F]
    [Fintype ι] [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (m : Word F ι) (hm : m ∈ elementaryCoboundaryMoves K) :
    m ∈ K.firstCoboundaryCheckCode.carrier := by
  classical
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
  exact (K.mem_firstCoboundaryCheckCode_iff _).2
    ⟨p.2 • canonicalBasisWord p.1, rfl⟩
end QEC.Coding.LocallyMinimalDistance
