-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.const_isScottContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:58:33.310823+00:00
-- url     : https://prove2.me/submissions/af13abb4-b37e-4277-bcc4-e2cd462f51d7

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_ofNat
import Theorems.Thm_Scott1976_DataTypesAsLattices_e_zero
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_botElem
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_e
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_topElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_botElem
attribute [local simp] Scott1976.DataTypesAsLattices.mem_e
attribute [local simp] Scott1976.DataTypesAsLattices.mem_topElem


attribute [local simp] Scott1976.DataTypesAsLattices.mem_ofNat

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (c : Pomega) :
    IsScottContinuous (fun _ : Pomega => c) := by
  intro x
  ext k
  constructor
  · intro hk
    exact mem_scottUnion.mpr ⟨0, by simp [e_zero], hk⟩
  · intro hk
    obtain ⟨_, _, hkn⟩ := mem_scottUnion.mp hk
    exact hkn
end Scott1976.DataTypesAsLattices
