-- Prove2me | solution 1 for Research.obliqueNormNum_ge_denominator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:03:18.937703+00:00
-- url     : https://prove2.me/submissions/0041c6fd-6bd2-4dab-92f6-8c382192c9b5

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
section
@[expose] public section
namespace Research
set_option maxRecDepth 100000
private lemma int_sq_ge_one {z : ℤ} (hz : z ≠ 0) : 1 ≤ z ^ 2 := by
  have hpos : 0 < z ^ 2 := sq_pos_of_ne_zero hz
  omega
end Research
end
end

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (m n : ℤ)
    (hne : (m, n) ≠ (0, 0)) : 305 ≤ obliqueNormNum (m, n) := by
  rw [obliqueNormNum_decomposition]
  by_cases hsum : m + n = 0
  · have hm : m ≠ 0 := by
      intro hm
      apply hne
      apply Prod.ext
      · exact hm
      · simpa [hm] using hsum
    have hn : n ≠ 0 := by
      intro hn
      apply hne
      apply Prod.ext
      · simpa [hn] using hsum
      · exact hn
    have hm2 := int_sq_ge_one hm
    have hn2 := int_sq_ge_one hn
    rw [hsum]
    norm_num
    omega
  · have hs2 := int_sq_ge_one hsum
    have hmn : 1 ≤ m ^ 2 + n ^ 2 := by
      by_cases hm : m = 0
      · subst m
        simpa using int_sq_ge_one (by
          intro hn
          exact hne (Prod.ext rfl hn))
      · have hm2 := int_sq_ge_one hm
        nlinarith [sq_nonneg n]
    nlinarith [sq_nonneg m, sq_nonneg n]
end Research
