-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_algebraMap_injective_5637b74125c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:31:28.831286+00:00
-- url     : https://prove2.me/submissions/87caf3af-2eae-49eb-9db5-767d785be007

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCompletionNormalDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCompletionNormalDescent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CompletionNormalDescent_eval__algebraMap_3e6113ca9a3f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open AdicCompletion Polynomial
variable {R : Type} [CommRing R] (J : Ideal R)
variable [IsNoetherianRing R]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace CompletionNormalDescent
theorem _root_.solution (hJ : J ≤ (⊥ : Ideal R).jacobson) :
    Function.Injective (algebraMap R (AdicCompletion J R)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have H : IsHausdorff J R := IsHausdorff.of_le_jacobson J R hJ
  refine H.haus a fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have := CompletionNormalDescent.evalₐ_algebraMap J n a
  rw [ha, _root_.map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this
end CompletionNormalDescent
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
