-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.restrict_finite_residueField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:31:02.902219+00:00
-- url     : https://prove2.me/submissions/1192be04-a1ab-451e-9a5b-704398b9b470

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.IsTrivialOn
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedRestriction

set_option autoImplicit false
open MonoidWithZeroHom
open scoped WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.GlobalPlace
noncomputable section
variable {k F E : Type*} [Field k] [Finite k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution [Algebra.IsAlgebraic F E]
    (Q : GlobalPlace k E) [Finite Q.residueField] :
    Finite (Q.restrict (F := F)).residueField := by
  let f := IsLocalRing.ResidueField.map (Q.restrictValuationRingMap (F := F))
  exact Finite.of_injective f f.injective
end QEC.Coding.AlgebraicGeometry.GlobalPlace
