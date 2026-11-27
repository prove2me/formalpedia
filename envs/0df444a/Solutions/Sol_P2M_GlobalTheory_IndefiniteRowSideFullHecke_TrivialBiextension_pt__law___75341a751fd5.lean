-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__law___75341a751fd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:52:21.571481+00:00
-- url     : https://prove2.me/submissions/cd9986f0-3619-41a8-9dc3-ad591fefb6a6

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
theorem _root_.solution {T : Over S} (a a' b : T ⟶ G) :
    (fun k => pt₃ G a a' b ≫ law₁φ G (x3 G 0) (x3 G 1) (x3 G 2) k) = law₁φ G a a' b := by
  funext ⟨k⟩
  fin_cases k <;> refine (pt₃_pt G _ _ _ _ _).trans ?_ <;>
    simp [law₁φ, padd, x3, comp_lift_assoc]
end GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
