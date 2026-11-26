-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_4_1_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:00:42.764801+00:00
-- url     : https://prove2.me/submissions/b1f68d6f-a7e6-445f-a8fd-629475f4a490

import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda
import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Theorems.Thm_Scott1976_DataTypesAsLattices_isScottContinuous_monotone
import Theorems.Thm_Scott1976_DataTypesAsLattices_mem_scottUnion
import Theorems.Thm_Scott1976_DataTypesAsLattices_theorem_1_4


set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (f : Pomega → Pomega) (hf : IsScottContinuous f)
    (A : Set Pomega) (_hA : A ⊆ Fixpoints f) :
    gfpBelow f (⋂₀ A) ∈ Fixpoints (fun z => f z ∩ ⋂₀ A) := by
  have hg : IsScottContinuous (fun z => f z ∩ ⋂₀ A) := by
    intro x
    ext k
    constructor
    · intro ⟨hkf, hkb⟩
      have : k ∈ scottUnion f x := by rwa [← hf x]
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, hkn, hkb⟩
    · intro hk
      obtain ⟨n, hn, hkn, hkb⟩ := mem_scottUnion.mp hk
      exact ⟨isScottContinuous_monotone hf hn hkn, hkb⟩
  change (fun z => f z ∩ ⋂₀ A) (gfpBelow f (⋂₀ A)) = gfpBelow f (⋂₀ A)
  exact (theorem_1_4 hg).1
end Scott1976.DataTypesAsLattices
