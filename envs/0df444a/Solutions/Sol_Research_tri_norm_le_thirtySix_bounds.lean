-- Prove2me | solution 1 for Research.tri_norm_le_thirtySix_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:03:38.743777+00:00
-- url     : https://prove2.me/submissions/a9f24f80-5abd-4ad1-bc99-f59e18cc770f

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix

set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder
namespace Research
theorem _root_.solution (m n : ℤ)
    (h : triNormSq (m, n) ≤ 36) :
    -6 ≤ m ∧ m ≤ 6 ∧ -6 ≤ n ∧ n ≤ 6 := by
  have hm2 : 3 * m ^ 2 ≤ 144 := by
    simp only [triNormSq] at h
    nlinarith [sq_nonneg (m + 2 * n)]
  have hn2 : 3 * n ^ 2 ≤ 144 := by
    simp only [triNormSq] at h
    nlinarith [sq_nonneg (2 * m + n)]
  constructor
  · by_contra hm
    have : m ≤ -7 := by omega
    nlinarith [sq_nonneg (m + 7)]
  constructor
  · by_contra hm
    have : 7 ≤ m := by omega
    nlinarith [sq_nonneg (m - 7)]
  constructor
  · by_contra hn
    have : n ≤ -7 := by omega
    nlinarith [sq_nonneg (n + 7)]
  · by_contra hn
    have : 7 ≤ n := by omega
    nlinarith [sq_nonneg (n - 7)]
end Research
