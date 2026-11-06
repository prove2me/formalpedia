-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:08:17.11504+00:00
-- url     : https://prove2.me/submissions/cb4ebb9f-e607-4858-aedd-234759017e78

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k K L : Type*} [Field k] [Finite k]
variable [Field K] [Algebra k K] [Field L] [Algebra k L]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution (e : K ≃ₐ[k] L)
    (P : GlobalPlace k L) (x : K) :
    (comapAlgEquiv e P).order x = P.order (e x) :=
  rfl
end QEC.Coding.AlgebraicGeometry.GlobalPlace
