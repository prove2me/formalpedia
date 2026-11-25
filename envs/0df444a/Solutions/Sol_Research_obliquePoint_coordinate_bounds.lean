-- Prove2me | solution 1 for Research.obliquePoint_coordinate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:07:09.37039+00:00
-- url     : https://prove2.me/submissions/d1fabeef-0581-48ed-a4a4-dc4f08303073

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
theorem _root_.solution (q : Fin 365 × Fin 365) :
    0 ≤ (obliquePoint q).1 ∧ (obliquePoint q).1 ≤ 600 ∧
      0 ≤ (obliquePoint q).2 ∧ (obliquePoint q).2 ≤ 400 := by
  have hq1N : q.1.val ≤ 364 := by omega
  have hq2N : q.2.val ≤ 364 := by omega
  have hq1 : (q.1.val : ℝ) ≤ 364 := by exact_mod_cast hq1N
  have hq2 : (q.2.val : ℝ) ≤ 364 := by exact_mod_cast hq2N
  have hq10 : (0 : ℝ) ≤ q.1.val := by positivity
  have hq20 : (0 : ℝ) ≤ q.2.val := by positivity
  simp only [obliquePoint]
  constructor
  · positivity
  · constructor
    · norm_num
      nlinarith
    · constructor
      · positivity
      · norm_num
        nlinarith
end Research
