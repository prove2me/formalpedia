-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.basis_query_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:18:48.492842+00:00
-- url     : https://prove2.me/submissions/92ed08cc-837f-4600-b224-1596ff32aabc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_basis_query_five_window
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26QuantitativeBounds_state_qubit_card_lower


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual (suffix_delta1)
open BDL26LocalBackgroundComparisonResponse BDL26PairedHistoryQueryCone
open MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
theorem _root_.solution (hn : 7 ≤ n) (odd : n % 2 = 1)
    (large : fiveStepPhysicalBudget S < 5*2^(n+2)) (q : Q S n) :
    queryMask S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
      (canonicalBasisWord (F:=BDL26Field) q) (canonicalBasisWord (F:=BDL26Field) q) ≠ Finset.univ := by
  intro hall
  have hb := (basis_query_five_window S n hn odd q).2.2
  rw [hall,Finset.card_univ] at hb
  have lower : 5*2^(n+2) ≤ Fintype.card (Q S n) :=
    BDL26QuantitativeBounds.state_qubit_card_lower S (n+2)
  omega
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
