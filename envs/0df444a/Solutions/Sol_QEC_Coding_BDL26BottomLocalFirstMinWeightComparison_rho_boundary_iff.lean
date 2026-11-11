-- Prove2me | solution 1 for QEC.Coding.BDL26BottomLocalFirstMinWeightComparison.rho_boundary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:44:25.970867+00:00
-- url     : https://prove2.me/submissions/a8b6e556-0b32-49f0-a952-d087d4144b09

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology_Equivalence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BottomLocalFirstMinWeightComparison
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_tanner_d1_d0
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_rho_boundary
import Theorems.Thm_QEC_Coding_BDL26BottomLocalFirstMinWeightComparison_lifted_boundary
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_rzCocycle_qParity_zero_is_coboundary
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
open BDL26FiniteTannerSquare BDL26FiniteAlternatingCore BDL26DecodingGraph
open BDL26TannerLocalRegularity BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26ReplacementCochainMaps BDL26LevelTwoCode BDL26LevelTwoDistance
open BDL26LevelTwoDecoder
open scoped BigOperators
namespace QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
theorem _root_.solution (S : OddScale) (w : Error S)
    (hw : tannerCoboundary1 (P2 S) w = 0) :
    w ∈ LinearMap.range (tannerCoboundary0 (P2 S)) ↔
      rho S w ∈ LinearMap.range (tannerCoboundary0 (P1 S)) := by
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨rzOldXParity (P1 S) S p,?_⟩
    exact (rho_boundary S p).symm.trans (congrArg (rho S) hp)
  · rintro ⟨p,hp⟩
    let liftedPotential : Word F (P2 S).X := rzMap0Coord (P1 S) S p
    have square : tannerCoboundary1 (P2 S)
        (tannerCoboundary0 (P2 S) liftedPotential) = 0 :=
      tanner_d1_d0 (P2 S) liftedPotential
    let residual : Error S := w-tannerCoboundary0 (P2 S) liftedPotential
    have hc : tannerCoboundary1 (P2 S) residual = 0 := by
      calc
        tannerCoboundary1 (P2 S) residual =
            tannerCoboundary1 (P2 S) w-
              tannerCoboundary1 (P2 S) (tannerCoboundary0 (P2 S) liftedPotential) :=
          map_sub (tannerCoboundary1 (P2 S)) _ _
        _ = 0 := by rw [hw,square,sub_self]
    have liftedParity : rho S (tannerCoboundary0 (P2 S) liftedPotential) =
        tannerCoboundary0 (P1 S) p :=
      (congrArg (rho S) (lifted_boundary S p)).trans
        (rzQParity_map1Coord (P1 S) (rxState S baseState).admissible S
          (tannerCoboundary0 (P1 S) p))
    have hrho : rho S residual = 0 := by
      calc
        rho S residual = rho S w-rho S (tannerCoboundary0 (P2 S) liftedPotential) :=
          map_sub (rho S) _ _
        _ = 0 := by rw [liftedParity,hp,sub_self]
    have actualFilling : ∃ fillingPotential : Word F (P2 S).X,
        tannerCoboundary0 (P2 S) fillingPotential = residual := by
      obtain ⟨rawPotential,rawBoundary⟩ := rzCocycle_qParity_zero_is_coboundary (P1 S)
        (rxState S baseState).admissible (rxState S baseState).regular S residual hc hrho
      let fillingPotential : Word F (P2 S).X := rawPotential
      refine ⟨fillingPotential,?_⟩
      funext coordinate
      exact congrFun rawBoundary coordinate
    obtain ⟨fillingPotential,actualBoundary⟩ := actualFilling
    refine ⟨fillingPotential+liftedPotential,?_⟩
    calc
      tannerCoboundary0 (P2 S) (fillingPotential+liftedPotential) =
          tannerCoboundary0 (P2 S) fillingPotential+
            tannerCoboundary0 (P2 S) liftedPotential :=
        (tannerCoboundary0 (P2 S)).map_add fillingPotential liftedPotential
      _ = residual+tannerCoboundary0 (P2 S) liftedPotential :=
        congrArg (fun a : Error S => a+tannerCoboundary0 (P2 S) liftedPotential)
          actualBoundary
      _ = w := sub_add_cancel _ _
end QEC.Coding.BDL26BottomLocalFirstMinWeightComparison
