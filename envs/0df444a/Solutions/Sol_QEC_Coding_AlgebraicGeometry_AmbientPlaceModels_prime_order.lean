-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AmbientPlaceModels.prime_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:35:55.144712+00:00
-- url     : https://prove2.me/submissions/067883a8-bb0d-4449-82e0-679c02f1b52e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
noncomputable section
variable {k E : Type*} [Field k] [Finite k] [Field E] [Algebra k E]
    (F : Type*) [Field F] [Algebra k F] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace k E)
namespace QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
theorem _root_.solution : (heightOnePlace (k := k) (K := E) (prime F Q)).order = Q.order :=
  (Classical.choose_spec (exists_prime F Q)).2
end QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
