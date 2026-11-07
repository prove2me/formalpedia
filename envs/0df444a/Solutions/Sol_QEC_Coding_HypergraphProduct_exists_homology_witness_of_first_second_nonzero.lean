-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.exists_homology_witness_of_first_second_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:40:05.701512+00:00
-- url     : https://prove2.me/submissions/3f93a060-c287-4380-90c8-b403c7b550aa

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordPairing_firstBlockWord
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordPairing_single_left
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordPairing_single_right
import Theorems.Thm_QEC_Coding_HypergraphProduct_hammingWeight_firstBlockWord_single_right
import Theorems.Thm_QEC_Coding_HypergraphProduct_firstBlockWord_mem_middleCycleCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_firstBlockWord_mem_middleCocycleCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_exists_apply_ne_zero_of_ne_zero
import Theorems.Thm_QEC_Coding_HypergraphProduct_not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u v
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (x : Word (ZMod 2) colOne) (hx : x ∈ (firstCode D).carrier)
    (hx0 : x ≠ 0)
    (y : Word (ZMod 2) colTwo) (hy : y ∈ (secondCode D).carrier)
    (hy0 : y ≠ 0) :
    ∃ z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo),
      z ∈ (chainComplex D).middleCycleCode.carrier ∧
      z ∉ (chainComplex D).middleBoundaryCode.carrier ∧
      HammingWeight z = HammingWeight x := by
  obtain ⟨c₁, hc₁⟩ := exists_apply_ne_zero_of_ne_zero x hx0
  obtain ⟨c₂, hc₂⟩ := exists_apply_ne_zero_of_ne_zero y hy0
  let z := firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
    x (Pi.single c₂ 1)
  let u := firstBlockWord (rowOne := rowOne) (rowTwo := rowTwo)
    (Pi.single c₁ 1) y
  have hzCycle : z ∈ (chainComplex D).middleCycleCode.carrier :=
    firstBlockWord_mem_middleCycleCode D x (Pi.single c₂ 1) hx
  have huCocycle : u ∈ (chainComplex D).middleCocycleCode.carrier :=
    firstBlockWord_mem_middleCocycleCode D (Pi.single c₁ 1) y hy
  have hPair : wordPairing u z ≠ 0 := by
    rw [wordPairing_firstBlockWord, wordPairing_single_left,
      wordPairing_single_right]
    exact mul_ne_zero hc₁ hc₂
  refine ⟨z, hzCycle,
    not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero
      D z u huCocycle hPair, ?_⟩
  exact hammingWeight_firstBlockWord_single_right x c₂
end QEC.Coding.HypergraphProduct
