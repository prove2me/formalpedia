-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_finiteType_sections_of_isFiniteTypeOverZ_dd9622bb96c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:10:34.673139+00:00
-- url     : https://prove2.me/submissions/b5c56568-cf5c-488f-be87-97b0f5c05218

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteTypeSectionsOfIsFiniteTypeOverZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution {X : Scheme.{0}} (hX : IsFiniteTypeOverZ X)
    {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  have := hX.1
  have h1 := (toSpecZ X).finiteType_appLE (isAffineOpen_top (Spec (.of ℤ))) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2
  have h3 := h1.comp h2
  rw [show ((toSpecZ X).appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom =
    algebraMap ℤ Γ(X, U) from RingHom.ext_int _ _] at h3
  exact RingHom.finiteType_algebraMap.mp h3
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
