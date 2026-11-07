-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.fundamentalIntegralConjugate_mem_integralGeneralLinearSet_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:28:51.805476+00:00
-- url     : https://prove2.me/submissions/bbb3944f-2123-4d6c-bfd2-fd7f56f3c07c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalIntegralConjugate_entries_mem_integer_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalIntegralConjugate_inv

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    fundamentalIntegralConjugate k d r g ∈ integralGeneralLinearSet k d ↔
      UpperRightResidueZero k d r g ∧
        UpperRightResidueZero k d r g⁻¹ := by
  change ((∀ i j, fundamentalIntegralConjugate k d r g i j ∈
      Valued.integer (LocalFunctionField k)) ∧
    ∀ i j, (fundamentalIntegralConjugate k d r g)⁻¹ i j ∈
      Valued.integer (LocalFunctionField k)) ↔ _
  rw [fundamentalIntegralConjugate_inv]
  exact and_congr
    (fundamentalIntegralConjugate_entries_mem_integer_iff k d r g)
    (fundamentalIntegralConjugate_entries_mem_integer_iff k d r g⁻¹)
end QEC.Coding.HighDimensionalExpander.SphericalHecke
