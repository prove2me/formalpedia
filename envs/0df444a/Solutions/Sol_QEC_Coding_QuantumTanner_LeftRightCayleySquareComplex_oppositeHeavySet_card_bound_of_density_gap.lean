-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.oppositeHeavySet_card_bound_of_density_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:18:46.448997+00:00
-- url     : https://prove2.me/submissions/bd57111f-30f9-4c0a-911e-fc55bbf49b50

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_cutoff_mul_oppositeHeavySet_card_le_crossCount
import Theorems.Thm_QEC_Coding_SmallSetExpansion_highDegree_card_bound_of_density_gap


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (spectral gap : ℝ) (hSpectral : 0 ≤ spectral) (hGap : 0 < gap)
    (hMixing : HasExpanderMixingBound X.unionCayleyGraph
      (Fintype.card A + Fintype.card B) spectral)
    (hDensity : ((Fintype.card A + Fintype.card B : Nat) : ℝ) *
        (X.activeVerticesOnSide side x).card + gap * Fintype.card G ≤
      (cutoff : ℝ) * Fintype.card G) :
    gap ^ 2 * (X.oppositeHeavySet side x cutoff normal).card ≤
      spectral ^ 2 * (X.activeVerticesOnSide side x).card := by
  apply highDegree_card_bound_of_density_gap X.unionCayleyGraph
    (Fintype.card A + Fintype.card B) spectral cutoff gap hSpectral hGap hMixing
    (X.oppositeHeavySet side x cutoff normal) (X.activeVerticesOnSide side x)
  · exact_mod_cast X.cutoff_mul_oppositeHeavySet_card_le_crossCount hX side x cutoff normal
  · exact hDensity
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
