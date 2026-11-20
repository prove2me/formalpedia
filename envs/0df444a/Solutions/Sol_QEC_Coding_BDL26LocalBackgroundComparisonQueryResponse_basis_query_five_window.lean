-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.basis_query_five_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:13:47.349609+00:00
-- url     : https://prove2.me/submissions/35b7d7c6-0134-433a-955a-095d7928f9da

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_queryMask_window_card
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_basis_syndrome_weight
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_five_step_coalescence
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_le_stoppingLevel


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
theorem _root_.solution (hn : 7 ≤ n) (odd : n % 2 = 1) (q : Q S n) :
    let zero := BDL26NonzeroBackgroundComparisonStability.zeroInput S n
    let e : W S n := canonicalBasisWord (F:=BDL26Field) q
    0 < (queryStop S n zero e e).val ∧
      n-(queryStop S n zero e e).val ≤ 5 ∧
      (queryMask S n zero e e).card ≤ fiveStepPhysicalBudget S := by
  let zero := BDL26NonzeroBackgroundComparisonStability.zeroInput S n
  let e : W S n := canonicalBasisWord (F:=BDL26Field) q
  have hc := le_stoppingLevel S n (perturbTop S n zero e) e ⟨n-5,by omega⟩
    (five_step_coalescence S n hn odd q)
  have hl : n-5 ≤ (queryStop S n zero e e).val := hc
  have hp : 0 < (queryStop S n zero e e).val := by omega
  have hw : n-(queryStop S n zero e e).val ≤ 5 := by omega
  exact ⟨hp,hw,queryMask_window_card S n zero e e 5 4 hp hw (basis_syndrome_weight S n q)⟩
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
