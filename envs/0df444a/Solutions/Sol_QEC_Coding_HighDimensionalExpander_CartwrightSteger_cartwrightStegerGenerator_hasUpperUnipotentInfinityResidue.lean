-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_hasUpperUnipotentInfinityResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:44:19.642063+00:00
-- url     : https://prove2.me/submissions/b05c4a75-e46a-44c7-a485-f00328c81188

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_mem_lattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_preservesInfinityCyclicLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_mem_filtration
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_conj_monomial


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    HasUpperUnipotentInfinityResidue P r
      (cartwrightStegerGenerator P r x) := by
  refine ⟨cartwrightStegerGenerator_preservesInfinityCyclicLattice P r x,
    ?_⟩
  intro k ζ
  have hformula := cartwrightStegerGenerator_conj_monomial P r x k ζ
  change
    infinityConjugationLinearMap P r (cartwrightStegerGenerator P r x)
        (constantMatrix P r ζ * cyclicGeneratorMatrix P r ^ (k : ℕ)) =
      infinityConjugationFormula P r
        (constantClassRepresentative P r x) (k : ℕ) ζ at hformula
  rw [hformula, infinityConjugationFormula]
  have hlower := infinityConjugationCorrectionSum_mem_filtration P r
    (constantClassRepresentative P r x) (k : ℕ) (k : ℕ)
    (Nat.le_of_lt k.isLt) ζ
  have htailLattice := infinityConjugationCorrectionSum_mem_lattice P r
    (constantClassRepresentative P r x) (k : ℕ) r.matrixRank (le_refl _) ζ
  have htail := infinityUniformizer_smul_mem_multiple P r htailLattice
  have htail' :
      (splittingY P r)⁻¹ •
          infinityConjugationCorrectionSum P r
            (constantClassRepresentative P r x) (k : ℕ) r.matrixRank ζ ∈
        InfinityUniformizerMultiple P r := by
    exact htail
  have hsum := Submodule.add_mem
    (InfinityCyclicFiltration P r (k : ℕ) ⊔ InfinityUniformizerMultiple P r)
    (Submodule.mem_sup_left hlower) (Submodule.mem_sup_right htail')
  convert hsum using 1
  abel
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
