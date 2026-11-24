-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_BaseChangeMin_flat_mvPolynomial_map_770f1c9d3b57
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:46.237854+00:00
-- url     : https://prove2.me/submissions/2a30266c-9966-4e38-9dbd-6bbfc663bc64

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_BaseChangeMinimal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
attribute [local instance] MvPolynomial.algebraMvPolynomial
omit [Fintype σ]
namespace GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
theorem _root_.solution :
    Module.Flat (MvPolynomial σ F) (MvPolynomial σ F') :=
  Module.Flat.isBaseChange F (MvPolynomial σ F) F' (MvPolynomial σ F')
    (Algebra.IsPushout.out (R := F) (S := MvPolynomial σ F) (R' := F') (S' := MvPolynomial σ F'))
end GroundTheory.Heights₂.Heights.Targets.BaseChangeMin
