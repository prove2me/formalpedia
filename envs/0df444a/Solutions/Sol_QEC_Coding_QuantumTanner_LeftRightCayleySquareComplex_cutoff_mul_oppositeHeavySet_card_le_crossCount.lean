-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.cutoff_mul_oppositeHeavySet_card_le_crossCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:14:47.836401+00:00
-- url     : https://prove2.me/submissions/79c8c7aa-8133-436e-a74a-42d35d4c7989

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_oppositeHeavySet_degree_lower
import Theorems.Thm_QEC_Coding_SmallSetExpansion_degree_mul_card_le_crossCount


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
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G) :
    cutoff * (X.oppositeHeavySet side x cutoff normal).card ≤
      crossCount X.unionCayleyGraph (X.oppositeHeavySet side x cutoff normal)
        (X.activeVerticesOnSide side x) := by
  apply degree_mul_card_le_crossCount
  exact X.oppositeHeavySet_degree_lower hX side x cutoff normal
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
