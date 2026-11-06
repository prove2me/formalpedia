-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.rationalDifferentialInvolution_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:37:47.190482+00:00
-- url     : https://prove2.me/submissions/1c364ded-125b-423e-93c2-b74f17f2e735

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_RationalInfinityTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueCoordinate
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InvolutionResidueTransport

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
open scoped Polynomial RatFunc WithZero
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
omit [Finite k]
namespace QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
theorem _root_.solution (f : RatFunc k)
    (omega : Differential k (RatFunc k)) :
    rationalDifferentialInvolution (k := k) (f • omega) =
      InverseAffinePlace.rationalInvolution k f •
        rationalDifferentialInvolution (k := k) omega := by
  change rationalDifferentialFromTarget (k := k)
      (rationalDifferentialToTarget (k := k) (f • omega)) =
    InverseAffinePlace.rationalInvolution k f •
      rationalDifferentialFromTarget (k := k)
        (rationalDifferentialToTarget (k := k) omega)
  rw [map_smul]
  change rationalDifferentialFromTarget (k := k)
      (algebraMap (RatFunc k) (RationalInvolutionTarget k) f •
        rationalDifferentialToTarget (k := k) omega) = _
  rw [map_smul]
  rfl
end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
