-- Prove2me | solution 1 for P2M_GlobalTheory_T_differentIdeal_pow_finrank_eq_span_discr__a357c7e2987b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:55:10.671651+00:00
-- url     : https://prove2.me/submissions/c0a33def-217e-4be3-b2c5-45aafb72d251

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentIdealPowFinrankEqSpanDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentIdealPowFinrankEqSpanDiscrStatement
import Theorems.Thm_GlobalTheory_GalDiff_differentIdeal_pow_finrank_eq_span_discr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F], differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by
  first | exact @GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | exact GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | (intros; apply GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr <;> assumption)
end _root_.GlobalTheory.T
