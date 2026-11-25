-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_le_ker_comp_subscheme__0da5f0ebbe52
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:49:02.778841+00:00
-- url     : https://prove2.me/submissions/863efea8-b078-42ac-a6a5-9aa6ba3f90fc

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
variable {P : Scheme.{u}}
private theorem comp_app_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (U : C.Opens) (x : Γ(C, U)) :
    ((f ≫ g).app U).hom x = (f.app (g ⁻¹ᵁ U)).hom ((g.app U).hom x) := rfl
private theorem subschemeι_app_apply_eq_zero {P : Scheme.{u}} (H : P.IdealSheafData)
    (U : P.affineOpens) (x : Γ(P, U.1)) (hx : x ∈ H.ideal U) :
    (H.subschemeι.app U.1).hom x = 0 := by
  have hpt : (H.subschemeι.app U.1).hom x
      = (H.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (H.ideal U) x) :=
    congrArg (fun g => CommRingCat.Hom.hom g x) (Scheme.IdealSheafData.subschemeι_app H U)
  rw [hpt, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
variable {k : Type u} [Field k]
end
section
variable {X : Scheme.{u}} {k : Type u} [Field k]
end
section
variable {P : Scheme.{u}} {k : Type u} [Field k]
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {P : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (H : P.IdealSheafData) (Z : H.subscheme.IdealSheafData) :
    H ≤ (Z.subschemeι ≫ H.subschemeι).ker := by
  simp only [Scheme.Hom.ker]
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
  intro U x hx
  simp only [RingHom.mem_ker]
  rw [comp_app_apply Z.subschemeι H.subschemeι U.1 x,
    subschemeι_app_apply_eq_zero H U x hx]
  exact map_zero _
end FunctorialResolution.EmbeddedResolution
