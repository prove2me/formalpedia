-- Prove2me | solution 1 for P2M_GlobalTheory_FormalAlg_TowerSq_thickTrans_thick__1d9f45897eeb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:30:30.724788+00:00
-- url     : https://prove2.me/submissions/c88077a9-6ffd-445f-abac-dd5e8326338a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TowerSquares

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FormalAlg GlobalTheory.FormalAlg.TowerSq
namespace GlobalTheory.FormalAlg.TowerSq
theorem _root_.solution (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) :
    thickTrans R I e ≫ thick R I (e + 1) = thick R I e := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl
end GlobalTheory.FormalAlg.TowerSq
