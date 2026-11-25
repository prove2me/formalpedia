-- Prove2me | solution 1 for P2M_GlobalTheory_HodgeTateTest_unitOf_one__c9598b6cdeb7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:49.345109+00:00
-- url     : https://prove2.me/submissions/8d9c8709-3d33-412e-b556-2e902dfa5679

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateTest
open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
variable {O : Type} [CommRing O]
namespace GlobalTheory.HodgeTateTest
theorem _root_.solution {R : Type} [CommRing R] [Algebra O R] :
    unitOf (1 : specO O R ⟶ GmO O) = 1 := by
  have h := unitOf_mul (1 : specO O R ⟶ GmO O) 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.mp h
end GlobalTheory.HodgeTateTest
