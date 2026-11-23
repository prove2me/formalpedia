-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:08.437667+00:00
-- url     : https://prove2.me/submissions/fe05cf43-ee02-49bd-9391-737d0859d124

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res

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
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {X Y Z Y' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
theorem _root_.solution (M N : LB X) (p p' : (LB.div M N).ι) (y : X)
    (hy : y ∈ (LB.div M N).U p ⊓ (LB.div M N).U p') :
    gU y hy ((LB.div M N).g p p') =
      gU y (⟨hy.1.1, hy.2.1⟩ : y ∈ M.U p.1 ⊓ M.U p'.1) (M.g p.1 p'.1) *
        (gU y (⟨hy.1.2, hy.2.2⟩ : y ∈ N.U p.2 ⊓ N.U p'.2) (N.g p.2 p'.2))⁻¹ := by
  have h1 : ((LB.div M N).U p ⊓ (LB.div M N).U p') ≤ M.U p.1 ⊓ M.U p'.1 := fun z hz => ⟨hz.1.1, hz.2.1⟩
  have h2 : ((LB.div M N).U p ⊓ (LB.div M N).U p') ≤ N.U p.2 ⊓ N.U p'.2 := fun z hz => ⟨hz.1.2, hz.2.2⟩
  have e : (LB.div M N).g p p' = res h1 (M.g p.1 p'.1) * (res h2 (N.g p.2 p'.2))⁻¹ := rfl
  exact (congrArg (gU y hy) e).trans ((map_mul (gU y hy) _ _).trans
    (congrArg₂ (· * ·) (gU_res h1 y hy _)
      ((map_inv (gU y hy) _).trans (congrArg (·⁻¹) (gU_res h2 y hy _)))))
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
