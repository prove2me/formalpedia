-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_res_5fd6dfc3c9f5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:51.151464+00:00
-- url     : https://prove2.me/submissions/d59f7662-41fd-4244-a6ae-bee7bf7b126c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules)
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {U V : Z.Opens} (h : V ≤ U) (i : g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ U) (m : Γ(M, U)) :
    pullSectionOn g M V ((M.presheaf.map (homOfLE h).op).hom m) =
      (((Scheme.Modules.pullback g).obj M).presheaf.map i.op).hom (pullSectionOn g M U m) := by
  have := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).mapPresheaf.naturality
    (homOfLE h).op
  have h2 := congrArg (fun φ => φ.hom m) this
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h2
  rw [Subsingleton.elim i ((Opens.map g.base).map (homOfLE h))]
  exact h2
end GroundTheory.Heights₂.Heights.Model
