-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SphericalHecke.residueFundamentalPlane_eq_iff_integralConjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:30:02.743741+00:00
-- url     : https://prove2.me/submissions/65e9f891-6272-4c87-a9eb-471b16304b32

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_CartanDecomposition
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalIntegralConjugate_mem_integralGeneralLinearSet_iff
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_residueFundamentalPlane_eq_iff_upperRight
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_upperRightResidueZero_inv_iff

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.FiniteGeometry
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
theorem _root_.solution
    (k : Type*) [Field k] (d r : ℕ) (hr : r ≤ d)
    (g h : GL (Fin d) (IntegerRing k)) :
    residueFundamentalPlane k d r hr g =
        residueFundamentalPlane k d r hr h ↔
      fundamentalIntegralConjugate k d r (g⁻¹ * h) ∈
        integralGeneralLinearSet k d := by
  rw [residueFundamentalPlane_eq_iff_upperRight,
    fundamentalIntegralConjugate_mem_integralGeneralLinearSet_iff]
  constructor
  · intro hinv
    exact ⟨(upperRightResidueZero_inv_iff k d r hr (g⁻¹ * h)).mp hinv,
      hinv⟩
  · exact fun hpair => hpair.2
end QEC.Coding.HighDimensionalExpander.SphericalHecke
