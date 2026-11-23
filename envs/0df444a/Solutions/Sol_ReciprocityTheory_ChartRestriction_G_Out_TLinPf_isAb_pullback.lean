-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:45.810012+00:00
-- url     : https://prove2.me/submissions/ae65fbf9-633e-4b83-86c0-424bb4abd405

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution {S S' : Scheme.{0}} (φ : S' ⟶ S) (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) : IsAbelianScheme ((Over.pullback φ).obj A) := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  exact
    { comm := Functor.isCommMonObj_obj
      smooth := by change Smooth (pullback.snd A.hom φ); infer_instance
      proper := by change IsProper (pullback.snd A.hom φ); infer_instance
      geomConnected := by change GeometricallyConnected (pullback.snd A.hom φ); infer_instance }
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
