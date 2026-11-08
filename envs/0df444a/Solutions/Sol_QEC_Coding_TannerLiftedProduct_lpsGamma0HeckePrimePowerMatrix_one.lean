-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGamma0HeckePrimePowerMatrix_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:31:18.254556+00:00
-- url     : https://prove2.me/submissions/5817e843-51e4-4839-acff-3866bf5c20a6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceFiniteDimension

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold Pointwise
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) : lpsGamma0HeckePrimePowerMatrix N p hNp 1 =
      lpsGamma0HeckeMatrix N p hNp := rfl
end QEC.Coding.TannerLiftedProduct
