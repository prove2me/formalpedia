-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceEdgeTower.original_correction_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:15:58.128427+00:00
-- url     : https://prove2.me/submissions/652ac714-01d2-4fd6-bd3a-e77d406fb747

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_full_potential_spec
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_full_potential_spec
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_full_potential_spec
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_full_potential_spec


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceEdgeTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXFaceEdgeTower
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) (hs : firstReadout S n u=0) :
    (SuffixData S n).family.coboundary0 (TopIndex n) (fullPotential S n u q t)=
      flip S n q+xCorrection S n u+xCorrection S n (translateX S n u (flip S n q)) := by
  rw [full_potential_spec S n u q t hs]
  unfold BDL26LogicalDefectProtection.deltaX BDL26ActualFailureReadout.flip
  ac_rfl
end QEC.Coding.BDL26RXFaceEdgeTower
