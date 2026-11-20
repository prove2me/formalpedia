-- Prove2me | solution 1 for QEC.Coding.BDL26NonzeroBackgroundComparisonStability.topPotential_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:46:58.692222+00:00
-- url     : https://prove2.me/submissions/03dee269-aaca-43b4-bfe1-3313cbc02d32

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Theorems.Thm_QEC_Coding_BDL26NonzeroBackgroundComparisonStability_terminalPotential_spec
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_localized_residual
import Theorems.Thm_QEC_Coding_BDL26AllDepthBottomComparisonStability_terminalPotential_spec
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap_commutes0
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NonzeroBackgroundComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual (suffix_delta0 suffix_delta1)
open BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26NonzeroBackgroundComparisonStability
theorem _root_.solution (S : OddScale) (n : Nat) (B : Nat)
    (large : 14*B+16 ≤ S.half) (sigma0 : TopInput S n)
    (zero : BDL26AllDepthBottomComparisonStability.baseReadout S n sigma0=0) (g : TopWord S n)
    (budget : HammingWeight g ≤ B) (e : TopWord S n) (x : (state S (n+2)).presentation.X)
    (support : hammingSupport e ⊆ BDL26LocalizedHistoryErrorDescent.star S n (TopIndex n) x) :
    (Data S n).family.coboundary0 (TopIndex n)
      (topPotential S n B large sigma0 zero g budget e x support)=
        BDL26AllDepthBottomComparisonStability.residual S n (perturbTop S n sigma0 g) e := by
  unfold topPotential
  rw [map_add,intervalMap_commutes0 _ n (Nat.le_refl _) 0 (Nat.zero_le _),terminalPotential_spec]
  exact (BDL26AllDepthBottomComparisonStability.localized_residual S n (perturbTop S n sigma0 g) e x support).symm
end QEC.Coding.BDL26NonzeroBackgroundComparisonStability
