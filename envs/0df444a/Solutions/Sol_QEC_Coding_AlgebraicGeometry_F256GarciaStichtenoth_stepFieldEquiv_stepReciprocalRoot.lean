-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepReciprocalRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:50:56.82604+00:00
-- url     : https://prove2.me/submissions/1e9e7d14-b500-4985-9627-cebed43411e7

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepTransport

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P Q : GlobalPlace F256 K) (x : K)
    (hP : P.order x = -1) (hQ : Q.order x = -1) :
    stepFieldEquiv P Q x hP hQ (stepReciprocalRoot P x hP) =
      stepReciprocalRoot Q x hQ := by
  exact AdjoinRoot.algEquivOfEq_root
    (stepPolynomial P x hP) (stepPolynomial Q x hQ)
    (stepPolynomial_eq_of_place P Q x hP hQ)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
