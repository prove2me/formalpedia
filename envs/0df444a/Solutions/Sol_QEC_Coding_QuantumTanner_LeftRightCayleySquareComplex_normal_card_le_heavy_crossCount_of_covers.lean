-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.normal_card_le_heavy_crossCount_of_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:10:43.050195+00:00
-- url     : https://prove2.me/submissions/9f684f16-5caf-4cad-a924-a6bca1f3bf7d

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_normal_card_le_heavy_crossCount
import Theorems.Thm_QEC_Coding_QuantumTanner_exists_heavy_line_of_cover


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
theorem _root_.solution
    (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B) (dA dB : Nat)
    (hA : HasMinimumDistanceAtLeast CA dA) (hB : HasMinimumDistanceAtLeast CB dB)
    (hNormal : normal ⊆ X.activeVerticesOnSide side x)
    (hCovers : ∀ g ∈ normal, ∃ rows : Finset A, ∃ columns : Finset B,
      X.localRestriction (g, side) x ∈ (dualTensorCode CA CB).carrier ∧
      SupportCovered (X.localRestriction (g, side) x) rows columns ∧
      rows.card < dA ∧ columns.card < dB ∧
      cutoff + columns.card ≤ dB ∧ cutoff + rows.card ≤ dA) :
    normal.card ≤ crossCount (X.heavyUnionGraph side x cutoff) normal
      (X.oppositeHeavySet side x cutoff normal) := by
  apply X.normal_card_le_heavy_crossCount side x cutoff normal
  intro g hg
  obtain ⟨rows, columns, hLocal, hCovered, hRows, hColumns, hCutoffRow, hCutoffColumn⟩ :=
    hCovers g hg
  exact exists_heavy_line_of_cover CA CB dA dB cutoff hA hB
    (X.localRestriction (g, side) x) hLocal (Finset.mem_filter.mp (hNormal hg)).2
    rows columns hRows hColumns hCovered hCutoffRow hCutoffColumn
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
