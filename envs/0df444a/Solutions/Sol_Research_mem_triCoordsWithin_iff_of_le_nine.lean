-- Prove2me | solution 1 for Research.mem_triCoordsWithin_iff_of_le_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:08:26.932064+00:00
-- url     : https://prove2.me/submissions/3897143e-8e36-4792-b5ff-e62e9578925a

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells
public import Theorems.Thm_Research_tri_norm_le_nine_bounds
public import Theorems.Thm_Research_mem_intWindow3_iff

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution (s : ℤ) (hs : s ≤ 9)
    (p : ℤ × ℤ) :
    p ∈ triCoordsWithin s ↔ p ≠ (0, 0) ∧ triNormSq p ≤ s := by
  rcases p with ⟨a, b⟩
  constructor
  · simp only [triCoordsWithin, Finset.mem_erase, Finset.mem_filter]
    rintro ⟨hne, _, hq⟩
    exact ⟨hne, hq⟩
  · rintro ⟨hne, hq⟩
    have hq9 : a ^ 2 + a * b + b ^ 2 ≤ 9 := le_trans hq hs
    have bounds := tri_norm_le_nine_bounds a b hq9
    rcases bounds with ⟨hal, hau, hbl, hbu⟩
    simp only [triCoordsWithin, Finset.mem_erase, Finset.mem_filter]
    exact ⟨hne, Finset.mem_product.mpr
      ⟨(mem_intWindow3_iff a).2 ⟨hal, hau⟩,
       (mem_intWindow3_iff b).2 ⟨hbl, hbu⟩⟩, hq⟩
end Research
