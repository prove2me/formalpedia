-- Prove2me | solution 1 for UpperTheory.GL.card_mul_delta_le_err
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:03:31.619876+00:00
-- url     : https://prove2.me/submissions/5a3d4e2b-a101-4f95-a5b9-94816c593c09

import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_ConductorsKronecker_CostPropositionBasicBound
import Theorems.Thm_UpperTheory_GL_cost_proposition_basic_bound

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
    (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ Cd CL Err : ℝ)
    (hH : GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err) (hS : SmallCosts x ε (fPl H) b η θ Cd CL) :
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ Err + 2 * (TT.card : ℝ) * m * b / x := by
  have hc := cost_proposition_basic_bound D S hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH
  obtain ⟨hMv, hth, hlip⟩ := hS
  have hx : 3 ≤ x := hH.1
  have hb : 0 < b := hH.2.1
  have hK : 0 ≤ (TT.card : ℝ) * m := by positivity
  have hδ : 0 ≤ delta2 T2 / 2 := by unfold delta2; positivity
  have h1 : (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ) ≤ (TT.card : ℝ) * m * (b * (1 / x)) := by
    apply mul_le_mul_of_nonneg_left _ hK
    calc 2 * fPl H * (x + 1) * b * θ = b * (2 * fPl H * (x + 1) * θ) := by ring
      _ ≤ b * (1 / x) := mul_le_mul_of_nonneg_left hth hb.le
  have h3 : (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1)) ≤ (TT.card : ℝ) * m * (b / x) :=
    mul_le_mul_of_nonneg_left hlip hK
  have e : 2 * (TT.card : ℝ) * m * b / x = (TT.card : ℝ) * m * (b * (1 / x)) + (TT.card : ℝ) * m * (b / x) := by
    ring
  rw [e]; linarith
end UpperTheory.GL
