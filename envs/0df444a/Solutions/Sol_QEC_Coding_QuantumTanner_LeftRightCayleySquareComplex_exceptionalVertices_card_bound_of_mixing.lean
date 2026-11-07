-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.exceptionalVertices_card_bound_of_mixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:48:17.520225+00:00
-- url     : https://prove2.me/submissions/70da93da-8f00-4e0c-9a10-d306dc95ba9d

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_exceptional_card_mul_cutoff_le_crossCount
import Theorems.Thm_QEC_Coding_SmallSetExpansion_highDegree_card_bound_of_mixing


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (cutoff : Nat) (threshold spectral : ℝ)
    (hThreshold : 0 < threshold) (hCutoff : threshold ≤ cutoff)
    (hSpectral : 0 ≤ spectral)
    (hMixing : HasExpanderMixingBound (X.squareGraph side)
      (Fintype.card A * Fintype.card B) spectral)
    (hSmall : 2 * ((Fintype.card A * Fintype.card B : Nat) : ℝ) *
      (X.activeVerticesOnSide side x).card ≤ threshold * Fintype.card G) :
    threshold ^ 2 * (X.exceptionalVerticesOnSide side x cutoff).card ≤
      4 * spectral ^ 2 * (X.activeVerticesOnSide side x).card := by
  apply highDegree_card_bound_of_mixing (X.squareGraph side)
    (Fintype.card A * Fintype.card B) spectral threshold hSpectral hThreshold hMixing
    (X.exceptionalVerticesOnSide side x cutoff) (X.activeVerticesOnSide side x) ?_ hSmall
  have hActual : (cutoff : ℝ) * (X.exceptionalVerticesOnSide side x cutoff).card ≤
      (crossCount (X.squareGraph side) (X.exceptionalVerticesOnSide side x cutoff)
        (X.activeVerticesOnSide side x) : ℝ) := by
    exact_mod_cast X.exceptional_card_mul_cutoff_le_crossCount side x cutoff
  exact (mul_le_mul_of_nonneg_right hCutoff (Nat.cast_nonneg _)).trans hActual
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
