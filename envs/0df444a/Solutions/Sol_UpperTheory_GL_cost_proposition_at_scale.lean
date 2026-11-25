-- Prove2me | solution 1 for UpperTheory.GL.cost_proposition_at_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:19:37.686406+00:00
-- url     : https://prove2.me/submissions/acc56cca-0847-4a7d-ab3c-d7b9860dce89

import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_CostPropositionBasicBound
import Theorems.Thm_UpperTheory_GL_card_mul_delta_le_err
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_proposition_size_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open UpperTheory UpperTheory.GL
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Deduction.CH
namespace UpperTheory.GL
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (S : Finset ℕ)
    (hD : HostFactsS D S) (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (C x ε b b' η X' θ Cd CL Err k aE : ℝ)
    (hH : GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err) (hS : SmallCosts x ε (fPl H) b η θ Cd CL)
    (hW : SizeWindows C ε x (Fintype.card H) TT.card T2.card m b k aE Err) :
    Gz x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) :=
  proposition_size_bound C ε x (Fintype.card H) TT.card T2.card m b k aE Err (Gz x) hW
    (card_mul_delta_le_err D S hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH hS)
end UpperTheory.GL
