-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__law___18ce999fa2e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:58:22.150379+00:00
-- url     : https://prove2.me/submissions/04f41b46-b0df-4642-a55c-4fa8790d9027

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_TrivialBiextension
import Theorems.Thm_P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__pt_cc9506f6e8c7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{u}} (G : Over S) [GrpObj G]
namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
theorem _root_.solution {T : Over S} (a b b' : T ⟶ G) :
    (fun k => pt₃ G a b b' ≫ law₂φ G (x3 G 0) (x3 G 1) (x3 G 2) k) = law₂φ G a b b' := by
  funext ⟨k⟩
  fin_cases k <;> refine (pt₃_pt G _ _ _ _ _).trans ?_ <;>
    simp [law₂φ, padd, x3, comp_lift_assoc]
end GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
