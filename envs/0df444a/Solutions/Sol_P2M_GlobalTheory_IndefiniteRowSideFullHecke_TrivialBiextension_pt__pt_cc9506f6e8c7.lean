-- Prove2me | solution 1 for P2M_GlobalTheory_IndefiniteRowSideFullHecke_TrivialBiextension_pt__pt_cc9506f6e8c7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:29.88391+00:00
-- url     : https://prove2.me/submissions/58acbfc7-b171-4206-acfe-d5b7c01eedb2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_TrivialBiextension

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
theorem _root_.solution {T : Over S} (a b c : T ⟶ G) (p q : G3 G ⟶ G) :
    pt₃ G a b c ≫ pt G p q = pt G (lift a (lift b c) ≫ p) (lift a (lift b c) ≫ q) := by
  rw [pt, pt, pt₃, ← Over.comp_left, comp_lift]
end GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
