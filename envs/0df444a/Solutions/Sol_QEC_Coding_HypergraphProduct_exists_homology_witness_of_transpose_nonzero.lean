-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.exists_homology_witness_of_transpose_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:40:07.358045+00:00
-- url     : https://prove2.me/submissions/49449ed6-84cc-4426-b5ce-cdc4347b9b41

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_LowerBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Locality
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Witness
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordPairing_secondBlockWord
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordPairing_single_left
import Theorems.Thm_QEC_Coding_HypergraphProduct_wordPairing_single_right
import Theorems.Thm_QEC_Coding_HypergraphProduct_hammingWeight_secondBlockWord_single_left
import Theorems.Thm_QEC_Coding_HypergraphProduct_secondBlockWord_mem_middleCycleCode
import Theorems.Thm_QEC_Coding_HypergraphProduct_secondBlockWord_mem_middleCocycleCode
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
    (x : Word (ZMod 2) rowOne)
    (hx : x ∈ (firstTransposeCode D).carrier) (hx0 : x ≠ 0)
    (y : Word (ZMod 2) rowTwo)
    (hy : y ∈ (secondTransposeCode D).carrier) (hy0 : y ≠ 0) :
    ∃ z : Word (ZMod 2) (QubitIndex rowOne colOne rowTwo colTwo),
      z ∈ (chainComplex D).middleCycleCode.carrier ∧
      z ∉ (chainComplex D).middleBoundaryCode.carrier ∧
      HammingWeight z = HammingWeight y := by
  obtain ⟨r₁, hr₁⟩ := exists_apply_ne_zero_of_ne_zero x hx0
  obtain ⟨r₂, hr₂⟩ := exists_apply_ne_zero_of_ne_zero y hy0
  let z := secondBlockWord (colOne := colOne) (colTwo := colTwo)
    (Pi.single r₁ 1) y
  let u := secondBlockWord (colOne := colOne) (colTwo := colTwo)
    x (Pi.single r₂ 1)
  have hzCycle : z ∈ (chainComplex D).middleCycleCode.carrier :=
    secondBlockWord_mem_middleCycleCode D (Pi.single r₁ 1) y hy
  have huCocycle : u ∈ (chainComplex D).middleCocycleCode.carrier :=
    secondBlockWord_mem_middleCocycleCode D x (Pi.single r₂ 1) hx
  have hPair : wordPairing u z ≠ 0 := by
    rw [wordPairing_secondBlockWord, wordPairing_single_right,
      wordPairing_single_left]
    exact mul_ne_zero hr₁ hr₂
  refine ⟨z, hzCycle,
    not_mem_middleBoundaryCode_of_pairing_cocycle_ne_zero
      D z u huCocycle hPair, ?_⟩
  exact hammingWeight_secondBlockWord_single_left r₁ y
end QEC.Coding.HypergraphProduct
