-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceEdgeTower.first_zero_chiX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:16:07.840738+00:00
-- url     : https://prove2.me/submissions/cd8e3058-9f74-4211-b1f7-ef48397e67d0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundaryTailInvariance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_full_potential_spec
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_chiX_top_coefficient
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_full_residual
import Theorems.Thm_QEC_Coding_BDL26BoundaryTailInvariance_full_potential_spec
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_full_potential_spec
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_full_potential_spec
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_top_zero_iff_boundary


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
    BDL26LogicalDefectProtection.chiX S n u q=0 := by
  rw [chiX_top_coefficient]
  apply (top_zero_iff_boundary S n (input S n u) (flip S n q)).mpr
  refine ⟨fullPotential S n u q t,?_⟩
  rw [full_residual]
  exact full_potential_spec S n u q t hs
end QEC.Coding.BDL26RXFaceEdgeTower
