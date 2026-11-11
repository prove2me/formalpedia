-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.ownerFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:56:09.373183+00:00
-- url     : https://prove2.me/submissions/7757af42-19a4-475e-b10b-76085cba0038

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_ownerFiber_rx
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_ownerFiber_rz_x_empty
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_ownerFiber_rz_q_empty
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rxSyndromeFiber_card_le
import Theorems.Thm_QEC_Coding_BDL26GraphQuantitativeBounds_rzSyndromeFiber_card_le
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

section
noncomputable section
namespace QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u
private theorem finite_card_independent {I : Type*} (F G : Fintype I) :
    @Fintype.card I F = @Fintype.card I G :=
  congrArg (fun e : Fintype I => @Fintype.card I e) (Subsingleton.elim F G)
private theorem ownerFiber_card_all (S : OddScale) (i : ℕ) (u : GraphVertex S i)
    (F : Fintype (OwnerFiber S i u)) : @Fintype.card (OwnerFiber S i u) F ≤ 14*S.ell^2 := by
  let : Fintype (OwnerFiber S i u) := F
  cases i with
  | zero =>
    have hEmpty : IsEmpty (OwnerFiber S 0 u) := ⟨fun c => PEmpty.elim c.val⟩
    exact le_trans (Fintype.card_eq_zero_iff.mpr hEmpty).le (Nat.zero_le _)
  | succ i => cases i with
    | zero =>
      have hEmpty : IsEmpty (OwnerFiber S 1 u) := ⟨fun c => PEmpty.elim c.val⟩
      exact le_trans (Fintype.card_eq_zero_iff.mpr hEmpty).le (Nat.zero_le _)
    | succ n =>
      by_cases h : (n+2)%2=1
      · exact (@Fintype.card_congr _ _ F _ (Equiv.cast (ownerFiber_rx S n h u))).le.trans
          ((finite_card_independent _ _).le.trans
            (rxSyndromeFiber_card_le _ (state_boundedValence S (n+1)) S u))
      · cases u with
        | x x =>
          exact le_trans
            (Fintype.card_eq_zero_iff.mpr (ownerFiber_rz_x_empty S n h x)).le (Nat.zero_le _)
        | q q =>
          exact le_trans
            (Fintype.card_eq_zero_iff.mpr (ownerFiber_rz_q_empty S n h q)).le (Nat.zero_le _)
        | z z =>
          exact (@Fintype.card_congr _ _ F _ (rzFiberEquiv S n h z)).le.trans
            ((finite_card_independent _ _).le.trans
              (rzSyndromeFiber_card_le _ (state S (n+1)).admissible.toTannerSquareAdmissible
                (state_boundedValence S (n+1)) S z))
end QEC.Coding.BDL26ConnectedSyndromeMass
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u
namespace QEC.Coding.BDL26ConnectedSyndromeMass
theorem _root_.solution (S : OddScale) (i : ℕ) (u : GraphVertex S i) :
    Fintype.card (OwnerFiber S i u) ≤ 14*S.ell^2 :=
  ownerFiber_card_all S i u _
end QEC.Coding.BDL26ConnectedSyndromeMass
