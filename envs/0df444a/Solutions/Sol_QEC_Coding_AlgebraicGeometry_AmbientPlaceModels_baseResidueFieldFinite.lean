-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.AmbientPlaceModels.baseResidueFieldFinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:47:14.461639+00:00
-- url     : https://prove2.me/submissions/13f5eb03-c860-44ae-9092-3e055374035a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RestrictedIntegralModel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_restrict_finite_residueField


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
noncomputable section
variable {k E : Type*} [Field k] [Finite k] [Field E] [Algebra k E]
    (F : Type*) [Field F] [Algebra k F] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (Q : GlobalPlace k E)
omit [FiniteDimensional F E]
namespace QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
theorem _root_.solution [Finite Q.residueField] :
    Finite (IsLocalRing.ResidueField (baseRing F Q)) :=
  Q.restrict_finite_residueField (F := F)
end QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
