-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.det_toMatrix_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:32.647294+00:00
-- url     : https://prove2.me/submissions/a5f54692-3650-437e-acf5-b17cce33c2ac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_IntegralModuleBasisStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Definitions.Def_ReciprocityTheory_ReducedBases_PrefixProdGeOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace Matrix ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open scoped MatrixOrder ComplexOrder
variable {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
theorem _root_.solution (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    (((Pi.basisFun ℤ (Fin d)).toMatrix e).det : ℝ) ^ 2 = 1 := by
  have h := (Pi.basisFun ℤ (Fin d)).toMatrix_mul_toMatrix_flip e
  have hu : IsUnit ((Pi.basisFun ℤ (Fin d)).toMatrix e).det :=
    isUnit_iff_exists_inv.mpr ⟨(e.toMatrix (Pi.basisFun ℤ (Fin d))).det,
      by rw [← Matrix.det_mul, h, Matrix.det_one]⟩
  rcases Int.isUnit_iff.mp hu with h1 | h1 <;> rw [h1] <;> norm_num
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
