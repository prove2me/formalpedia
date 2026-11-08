-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegralCuspHecke_exists_monic_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:32:41.944893+00:00
-- url     : https://prove2.me/submissions/cca0c105-40b3-48ab-93df-7578b3e4882f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspIntegralHecke
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralCuspLattice_finite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Polynomial
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) :
    ∃ P : ℤ[X], P.Monic ∧ aeval (lpsIntegralCuspHecke N p hNp) P = 0 := by
  let := lpsIntegralCuspLattice_finite N
  exact LinearMap.exists_monic_and_aeval_eq_zero ℤ (lpsIntegralCuspHecke N p hNp)
end QEC.Coding.TannerLiftedProduct
