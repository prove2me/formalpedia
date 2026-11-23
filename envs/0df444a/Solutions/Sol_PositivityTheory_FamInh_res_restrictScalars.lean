-- Prove2me | solution 1 for PositivityTheory.FamInh.res_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:33.342704+00:00
-- url     : https://prove2.me/submissions/2043e785-420d-4fb8-94de-2bb8ada9b2d0

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_WeilBound_CoreStatements_PlaceConnectedComponents_ArtinA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open PositivityTheory PositivityTheory.FamInh
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
variable [IsGalois K L]
omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
namespace PositivityTheory.FamInh
theorem _root_.solution (g : Ω ≃ₐ[L] Ω) : AlgEquiv.restrictNormalHom L (g.restrictScalars K : G K Ω) = 1 := by
  ext x
  apply (algebraMap L Ω).injective
  exact (AlgEquiv.restrictNormal_commutes (g.restrictScalars K) L x).trans (g.commutes x)
end PositivityTheory.FamInh
