-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.charOpen_isScottContinuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:02:23.533861+00:00
-- url     : https://prove2.me/submissions/91130e47-eee5-4ada-97e1-eb42d31f565f

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Classification
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (U : Set Pomega) :
    IsScottContinuous (charOpen U) := by
  intro x
  ext k
  constructor
  · intro ⟨hk0, n, hn, hne⟩
    exact mem_scottUnion.mpr ⟨n, hn, hk0, n, subset_rfl, hne⟩
  · intro hk
    obtain ⟨m, hm, hk0, n, hn, hne⟩ := mem_scottUnion.mp hk
    exact ⟨hk0, n, subset_trans hn hm, hne⟩
end Scott1976.DataTypesAsLattices
