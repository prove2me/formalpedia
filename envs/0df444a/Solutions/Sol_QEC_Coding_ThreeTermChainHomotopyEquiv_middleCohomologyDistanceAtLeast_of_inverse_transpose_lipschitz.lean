-- Prove2me | solution 1 for QEC.Coding.ThreeTermChainHomotopyEquiv.middleCohomologyDistanceAtLeast_of_inverse_transpose_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:48:06.949502+00:00
-- url     : https://prove2.me/submissions/84397020-e987-4bc4-90c9-fd096d2df678

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Theorems.Thm_QEC_Coding_ThreeTermChainHomotopyEquiv_inverse_transpose_map1_not_mem_firstCoboundaryCheckCode

set_option autoImplicit false
open QEC QEC.Coding
universe u v w
open QEC.Coding.ThreeTermChainHomotopyEquiv
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {ι0 ι1 ι2 : Type v} [Fintype ι0] [Fintype ι1] [Fintype ι2]
variable {κ0 κ1 κ2 : Type w} [Fintype κ0] [Fintype κ1] [Fintype κ2]
variable {A : ChainComplexData F (Word F ι0) (Word F ι1) (Word F ι2)}
variable {B : ChainComplexData F (Word F κ0) (Word F κ1) (Word F κ2)}
namespace QEC.Coding.ThreeTermChainHomotopyEquiv
theorem _root_.solution
    (e : ThreeTermChainHomotopyEquiv A B)
    {d L : Nat}
    (hTarget : MiddleCohomologyDistanceAtLeast B d)
    (hLipschitz : ∀ x : Word F ι1,
      HammingWeight (wordLinearMapTranspose e.inverse.map1 x) ≤
        L * HammingWeight x) :
    MiddleCohomologyDistanceAtLeast A (d / L) := by
  change ∀ x : Word F ι1,
    x ∈ A.middleCocycleCode.carrier →
    x ∉ A.firstCoboundaryCheckCode.carrier →
    d / L ≤ HammingWeight x
  intro x hxCocycle hxNontrivial
  apply Nat.div_le_of_le_mul
  exact (hTarget (wordLinearMapTranspose e.inverse.map1 x)
    (e.inverse.mapMiddleCocycle ⟨x, hxCocycle⟩).2
    (e.inverse_transpose_map1_not_mem_firstCoboundaryCheckCode
      hxCocycle hxNontrivial)).trans (hLipschitz x)
end QEC.Coding.ThreeTermChainHomotopyEquiv
