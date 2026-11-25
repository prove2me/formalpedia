-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.germ_pullU_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:24:04.918127+00:00
-- url     : https://prove2.me/submissions/3b230e3b-2155-437a-b01f-f50faa8ee9bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res

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
theorem _root_.solution (M N : LB X) (a : Y ⟶ X) (p p' : (LB.div M N).ι) (y : Y)
    (hy : y ∈ a ⁻¹ᵁ ((LB.div M N).U p ⊓ (LB.div M N).U p'))
    (h1 : y ∈ a ⁻¹ᵁ (M.U p.1 ⊓ M.U p'.1)) (h2 : y ∈ a ⁻¹ᵁ (N.U p.2 ⊓ N.U p'.2)) :
    gU y hy (pullU a _ ((LB.div M N).g p p')) =
      gU y h1 (pullU a _ (M.g p.1 p'.1)) * (gU y h2 (pullU a _ (N.g p.2 p'.2)))⁻¹ := by
  have k1 : ((LB.div M N).U p ⊓ (LB.div M N).U p') ≤ M.U p.1 ⊓ M.U p'.1 := fun z hz => ⟨hz.1.1, hz.2.1⟩
  have k2 : ((LB.div M N).U p ⊓ (LB.div M N).U p') ≤ N.U p.2 ⊓ N.U p'.2 := fun z hz => ⟨hz.1.2, hz.2.2⟩
  have e : (LB.div M N).g p p' = res k1 (M.g p.1 p'.1) * (res k2 (N.g p.2 p'.2))⁻¹ := rfl
  exact (congrArg (fun z => gU y hy (pullU a ((LB.div M N).U p ⊓ (LB.div M N).U p') z)) e).trans
    (((congrArg (gU y hy) (map_mul (pullU a ((LB.div M N).U p ⊓ (LB.div M N).U p')) _ _)).trans (map_mul (gU y hy) _ _)).trans
      (congrArg₂ (· * ·) (gU_pullU_res a k1 (M.g p.1 p'.1) y hy h1)
        ((congrArg (gU y hy) (map_inv (pullU a ((LB.div M N).U p ⊓ (LB.div M N).U p')) _)).trans ((map_inv (gU y hy) _).trans
          (congrArg (·⁻¹) (gU_pullU_res a k2 (N.g p.2 p'.2) y hy h2))))))
end ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
