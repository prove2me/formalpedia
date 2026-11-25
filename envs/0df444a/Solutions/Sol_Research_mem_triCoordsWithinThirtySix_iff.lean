-- Prove2me | solution 1 for Research.mem_triCoordsWithinThirtySix_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:08:48.297916+00:00
-- url     : https://prove2.me/submissions/76fb8106-aabd-4243-8f4d-67e95116452f

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
public import Theorems.Thm_Research_tri_norm_le_thirtySix_bounds

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (d : ℤ × ℤ) :
    d ∈ triCoordsWithinThirtySix ↔
      d ≠ (0, 0) ∧ triNormSq d ≤ 36 := by
  rcases d with ⟨m, n⟩
  constructor
  · intro h
    have he := Finset.mem_erase.mp h
    exact ⟨he.1, (Finset.mem_filter.mp he.2).2⟩
  · intro h
    have hb := tri_norm_le_thirtySix_bounds m n h.2
    apply Finset.mem_erase.mpr
    refine ⟨h.1, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h.2⟩⟩
    · exact (mem_intWindow6_iff m).2 ⟨hb.1, hb.2.1⟩
    · exact (mem_intWindow6_iff n).2 ⟨hb.2.2.1, hb.2.2.2⟩
end Research
