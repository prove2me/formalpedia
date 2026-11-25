-- Prove2me | solution 1 for Research.triCoordsWithinReal_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:58:28.029577+00:00
-- url     : https://prove2.me/submissions/46ba05c9-76cf-4054-8e13-fa111c050355

module
public import Definitions.Def_Research_Basic
public import Definitions.Def_Research_TriangularShells

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution (s : ℝ) (h2 : 2 ≤ s) (h3 : s < 3) :
    triCoordsWithinReal s = triCoordsWithin 2 := by
  ext p
  simp only [triCoordsWithinReal, triCoordsWithin, Finset.mem_erase,
    Finset.mem_filter]
  constructor
  · rintro ⟨hne, hwin, hq⟩
    refine ⟨hne, hwin, ?_⟩
    have hqR : (triNormSq p : ℝ) < 3 := lt_of_le_of_lt hq h3
    have hqZ : triNormSq p < 3 := by exact_mod_cast hqR
    omega
  · rintro ⟨hne, hwin, hq⟩
    refine ⟨hne, hwin, ?_⟩
    have hqR : (triNormSq p : ℝ) ≤ 2 := by exact_mod_cast hq
    exact hqR.trans h2
end Research
