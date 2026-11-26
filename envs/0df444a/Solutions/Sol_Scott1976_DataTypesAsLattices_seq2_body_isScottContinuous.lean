-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.seq2_body_isScottContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:34.664394+00:00
-- url     : https://prove2.me/submissions/083f6be0-ea53-49ef-b39d-f421a793bae7

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_predSet_isScottContinuous
import Theorems.Thm_Scott1976_DataTypesAsLattices_condSet_isScottContinuous_left
import Theorems.Thm_Scott1976_DataTypesAsLattices_condSet_isScottContinuous_right
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_3_diag
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem


attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (x y : Pomega) :
    IsScottContinuous (fun z => condSet z x (condSet (predSet z) y botElem)) := by
  intro z
  have H := theorem_1_3_diag (x := z)
    (f := fun z w => condSet z x (condSet (predSet w) y botElem))
    (fun _w => condSet_isScottContinuous_left x _)
    (fun _z =>
      theorem_1_3 (condSet_isScottContinuous_right _z x)
        (theorem_1_3 (condSet_isScottContinuous_left y botElem)
          predSet_isScottContinuous))
  ext k
  constructor
  · intro hk
    have : k ∈ ⋃ n, {k | e n ⊆ z ∧
        k ∈ condSet (e n) x (condSet (predSet (e n)) y botElem)} := by
      rwa [← H]
    obtain ⟨n, hn, hkn⟩ := Set.mem_iUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    have : k ∈ ⋃ n, {k | e n ⊆ z ∧
        k ∈ condSet (e n) x (condSet (predSet (e n)) y botElem)} :=
      Set.mem_iUnion.mpr ⟨n, hn, hkn⟩
    rwa [← H] at this
end Scott1976.DataTypesAsLattices
