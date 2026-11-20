-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroEmptySuffix.first_zero_chiX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:21:23.880267+00:00
-- url     : https://prove2.me/submissions/b8e69d86-35cc-4007-88f6-5782cc0f591e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroFaceEndpoint
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_full_potential_spec
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_chiX_top_coefficient
import Theorems.Thm_QEC_Coding_BDL26ActualFailureReadout_full_residual
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_top_zero_iff_boundary


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroEmptySuffix
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroEmptySuffix
theorem _root_.solution (S : OddScale) (u : XSyndromeDomain S 0) (q : Physical S 2)
    (hs : firstReadout S 0 u=0) : BDL26LogicalDefectProtection.chiX S 0 u q=0 := by
  rw [chiX_top_coefficient]
  apply (top_zero_iff_boundary S 0 (input S 0 u) (flip S 0 q)).mpr
  refine ⟨fullPotential S u q,?_⟩
  rw [full_residual]
  exact full_potential_spec S u q hs
end QEC.Coding.BDL26FirstZeroEmptySuffix
