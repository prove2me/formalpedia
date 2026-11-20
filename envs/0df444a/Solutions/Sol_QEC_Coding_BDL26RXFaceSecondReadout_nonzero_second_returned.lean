-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.nonzero_second_returned
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:23:07.45161+00:00
-- url     : https://prove2.me/submissions/5033543e-d7f5-46ee-8ffa-e9ac4bdcbe6c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_second_returned
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_second_returned
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_second_returned
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXFaceSecondReadout
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : BDL26RXFaceEdgeTower.Tower S n q)
    (hfirst : firstReadout S n u=0) (hsecond : secondReadout S n u q≠0) :
    ∃ w : Word F (BDL26LevelTwoDecoder.ExecutableQ S),
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S n u q)=some w ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q)) ∧
      BDL26RXFaceEdgeTower.delta S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q))=
        secondReadout S n u q ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)≠0 := by
  obtain ⟨w,hw,he,hl,hd⟩ := BDL26RXFaceEdgeTower.second_returned S n u q t hfirst
  refine ⟨w,hw,he,hl,hd,?_⟩
  intro hz
  apply hsecond
  exact hd.symm.trans ((congrArg (BDL26RXFaceEdgeTower.delta S) hz).trans (map_zero _))
end QEC.Coding.BDL26RXFaceSecondReadout
