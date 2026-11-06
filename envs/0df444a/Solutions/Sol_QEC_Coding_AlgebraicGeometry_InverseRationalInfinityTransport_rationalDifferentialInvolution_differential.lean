-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport.rationalDifferentialInvolution_differential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:37:40.345499+00:00
-- url     : https://prove2.me/submissions/643d8351-6af0-4d4f-9dc3-94d685565b27

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
theorem _root_.solution (f : RatFunc k) :
    rationalDifferentialInvolution (k := k) (differential k (RatFunc k) f) =
      differential k (RatFunc k) (InverseAffinePlace.rationalInvolution k f) := by
  change rationalDifferentialFromTarget (k := k)
      (rationalDifferentialToTarget (k := k)
        (KaehlerDifferential.D k (RatFunc k) f)) =
    KaehlerDifferential.D k (RatFunc k)
      (InverseAffinePlace.rationalInvolution k f)
  rw [show rationalDifferentialToTarget (k := k)
        (KaehlerDifferential.D k (RatFunc k) f) =
      KaehlerDifferential.D k (RationalInvolutionTarget k)
        (algebraMap (RatFunc k) (RationalInvolutionTarget k) f) by
    exact KaehlerDifferential.map_D k k (RatFunc k)
      (RationalInvolutionTarget k) f]
  rw [show rationalDifferentialFromTarget (k := k)
        (KaehlerDifferential.D k (RationalInvolutionTarget k)
          (algebraMap (RatFunc k) (RationalInvolutionTarget k) f)) =
      KaehlerDifferential.D k (RatFunc k)
        (algebraMap (RationalInvolutionTarget k) (RatFunc k)
          (algebraMap (RatFunc k) (RationalInvolutionTarget k) f)) by
    exact KaehlerDifferential.map_D k k (RationalInvolutionTarget k)
      (RatFunc k) (algebraMap (RatFunc k) (RationalInvolutionTarget k) f)]
  rfl
end QEC.Coding.AlgebraicGeometry.InverseRationalInfinityTransport
