-- Prove2me | solution 1 for P2M_GlobalTheory_T_eq_map_maximalIdeal_of_ringKrullDim_eq_one__f360875eaa41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:09.088257+00:00
-- url     : https://prove2.me/submissions/0b111f26-7932-49ce-8c16-36364fe52961

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqMapMaximalIdealOfRingKrullDimEqOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqMapMaximalIdealOfRingKrullDimEqOneStatement
import Theorems.Thm_GlobalTheory_eq_map_maximalIdeal_of_ringKrullDim_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A] (p : Ideal A) [p.IsPrime], (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 → IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) → p = (maximalIdeal R).map (algebraMap R A) := by
  first | exact @GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one | exact GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one | (intros; apply GlobalTheory.eq_map_maximalIdeal_of_ringKrullDim_eq_one <;> assumption)
end _root_.GlobalTheory.T
