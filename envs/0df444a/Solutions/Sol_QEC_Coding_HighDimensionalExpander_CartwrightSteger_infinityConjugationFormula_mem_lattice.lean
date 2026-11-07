-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationFormula_mem_lattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:34:31.627435+00:00
-- url     : https://prove2.me/submissions/e1e4939f-a365-4cf1-bd61-da3bb45f0a59

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_mem_lattice

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (hk : k < r.matrixRank) (ζ : ConstantExtension P r) :
    infinityConjugationFormula P r u k ζ ∈
      InfinityCyclicLattice P r := by
  rw [infinityConjugationFormula]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact cyclicMonomial_mem_infinityCyclicLattice P r ζ k hk
    · exact infinityConjugationCorrectionSum_mem_lattice P r u k k
        (Nat.le_of_lt hk) ζ
  · have htail := infinityConjugationCorrectionSum_mem_lattice P r u k
      r.matrixRank (le_refl _) ζ
    have hsmul := (InfinityCyclicLattice P r).smul_mem
      (infinityUniformizer P r) htail
    exact hsmul
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
