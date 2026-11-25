-- Prove2me | solution 1 for P2M_GlobalTheory_FormalAlg_TowerSq_mono_thick__4223908ece3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:32:01.578097+00:00
-- url     : https://prove2.me/submissions/39cf5447-81fe-4ddf-afcf-375da8f90d17

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
theorem _root_.solution (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance
end GlobalTheory.FormalAlg.TowerSq
