-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.radius_error_light_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:53:52.426207+00:00
-- url     : https://prove2.me/submissions/31340892-66f1-4e42-81d1-cefe4582a200

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_rho_weight_le
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_boundary_of_closed_rho_weight
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_sameSyndrome_add_cocycle
import Theorems.Thm_QEC_Coding_HammingWeight_add_le
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (r : Nat)
    (large : 2*r+2 ≤ S.half) (e c : Error S)
    (small : HammingWeight e ≤ r) (light : HammingWeight c ≤ HammingWeight e)
    (same : tannerCoboundary1 (P2 S) c = tannerCoboundary1 (P2 S) e) :
    e+c ∈ LinearMap.range (tannerCoboundary0 (P2 S)) := by
  apply boundary_of_closed_rho_weight S (2*r) large (e+c)
    (sameSyndrome_add_cocycle S e c same.symm)
  have he := rho_weight_le S e
  have hc := rho_weight_le S c
  have ha := HammingWeight_add_le (rho S e) (rho S c)
  have sum : rho S (e+c)=rho S e+rho S c := (rho S).map_add e c
  rw [sum]
  omega
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
