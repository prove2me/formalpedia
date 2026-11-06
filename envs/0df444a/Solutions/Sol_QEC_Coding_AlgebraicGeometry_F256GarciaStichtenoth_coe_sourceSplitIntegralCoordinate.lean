-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:00:46.598229+00:00
-- url     : https://prove2.me/submissions/9748d5b0-dc78-409d-8b9e-6a42790db519

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitIntegralClosure

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0) :
    (sourceSplitIntegralCoordinate Q P x hx hregular hsplit :
        SourceStepField P x hx) = sourceStepCoordinate P x hx :=
  rfl
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
