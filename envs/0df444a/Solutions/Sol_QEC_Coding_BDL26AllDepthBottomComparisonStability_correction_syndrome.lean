-- Prove2me | solution 1 for QEC.Coding.BDL26AllDepthBottomComparisonStability.correction_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:31:49.176901+00:00
-- url     : https://prove2.me/submissions/0ee5f356-a62f-4845-bb64-7cc7d95a26ed

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4OldXEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_baseComparison_syndrome
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_intervalCocycle_word
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualHistory_syndrome
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_word_add_self
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

section
noncomputable section
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
private theorem interval_closed (S : OddScale) (n : Nat) (w : BaseWord S n)
    (closed : (Data S n).family.coboundary1 0 w=0) :
    (Data S n).family.coboundary1 (TopIndex n)
      (intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) w)=0 := by
  let wNative : Word F (state S 2).presentation.Q := fun q => w q
  have closedNative : tannerCoboundary1 (state S 2).presentation wNative = 0 :=
    (LinearMap.congr_fun (suffix_delta1 S n (0 : LevelIndex n)) w).symm.trans closed
  let c : BDL26FiniteCohomology.Cocycle S 2 :=
    ⟨wNative,(BDL26RZCohomology.mem_cocycle_iff
      (state S 2).presentation wNative).mpr closedNative⟩
  let upper : BDL26FiniteCohomology.Cocycle S ((TopIndex n).val+2) :=
    intervalCocycle S n 0 (TopIndex n) (Nat.zero_le _) c
  have upperClosed : tannerCoboundary1
      (state S ((TopIndex n).val+2)).presentation upper.val = 0 :=
    (BDL26RZCohomology.mem_cocycle_iff
      (state S ((TopIndex n).val+2)).presentation upper.val).mp upper.property
  have wordNative : upper.val =
      (fun q => intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) w q) :=
    intervalCocycle_word S n 0 (TopIndex n) (Nat.zero_le _) c
  have liftedClosed : tannerCoboundary1 (state S ((TopIndex n).val+2)).presentation
      (fun q => intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) w q) = 0 :=
    (congrArg (tannerCoboundary1 (state S ((TopIndex n).val+2)).presentation)
      wordNative).symm.trans upperClosed
  exact (LinearMap.congr_fun (suffix_delta1 S n (TopIndex n))
    (intervalMap1 (Data S n) 0 (TopIndex n) (Nat.zero_le _) w)).trans liftedClosed
end QEC.Coding.BDL26AllDepthBottomComparisonStability
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26AllDepthBottomComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26AllDepthBottomComparisonStability
theorem _root_.solution (S : OddScale) (n : Nat) (sigma : TopInput S n) :
    (Data S n).family.coboundary1 (TopIndex n) (correction S n sigma)=sigma.val := by
  have hb := (actualBase S n).rightInverse (actualInputs S n sigma 0)
  have hc := baseComparison_syndrome S n sigma
  have hclosed : (Data S n).family.coboundary1 0
      ((actualBase S n).decode (actualInputs S n sigma 0)+baseComparison S n sigma)=0 := by
    rw [map_add,hb,hc]
    exact word_add_self _
  unfold correction
  rw [map_add,interval_closed S n _ hclosed,add_zero]
  exact actualHistory_syndrome S n sigma
end QEC.Coding.BDL26AllDepthBottomComparisonStability
