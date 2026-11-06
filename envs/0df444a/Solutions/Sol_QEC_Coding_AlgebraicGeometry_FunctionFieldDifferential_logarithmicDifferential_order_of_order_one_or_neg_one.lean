-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.logarithmicDifferential_order_of_order_one_or_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:01:56.273821+00:00
-- url     : https://prove2.me/submissions/30d4f4ce-0442-4ccc-9c78-c3f6ca5f9324

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ParameterDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_logarithmicDifferential_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_logarithmicDifferential


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
noncomputable section
variable {k K : Type*} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [Algebra.IsSeparable (RatFunc k) K] [FiniteDimensional (RatFunc k) K]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution
    (P : GlobalPlace k K) (f : K) (hf : f ≠ 0)
    (horder : P.order f = 1 ∨ P.order f = -1) :
    differentialOrder P (Differential.logarithmicDifferential (k := k) f)
      (logarithmicDifferential_ne_zero_of_order_one_or_neg_one P f hf horder) = -1 := by
  let omega := Differential.logarithmicDifferential (k := k) f
  let homega := logarithmicDifferential_ne_zero_of_order_one_or_neg_one P f hf horder
  have hsimple : omega ∈ Differential.simplePoleDifferentialLattice P :=
    Differential.logarithmicDifferential_isGlobalSimplePole f hf P
  have hres : Differential.simplePoleResidue P
      (Differential.logarithmicDifferentialAtSimplePole P f hf) ≠ 0 := by
    rw [Differential.simplePoleResidue_logarithmicDifferential]
    rcases horder with horder | horder <;> rw [horder] <;> norm_num
  have hnot : omega ∉ Differential.localDifferentialLattice P := by
    intro hreg
    exact hres (Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice P
      (Differential.logarithmicDifferentialAtSimplePole P f hf) hreg)
  have hge := (Differential.mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
    P omega homega).mp hsimple
  have hlt : ¬ 0 ≤ differentialOrder P omega homega := by
    intro hn
    exact hnot ((Differential.mem_localDifferentialLattice_iff_differentialOrder_nonnegative
      P omega homega).mpr hn)
  change differentialOrder P omega homega = -1
  omega
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
