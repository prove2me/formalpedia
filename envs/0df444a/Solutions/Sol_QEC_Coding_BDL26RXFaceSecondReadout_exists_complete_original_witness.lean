-- Prove2me | solution 1 for QEC.Coding.BDL26RXFaceSecondReadout.exists_complete_original_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:43:11.101185+00:00
-- url     : https://prove2.me/submissions/e420801d-7970-461c-ba1e-a105f92c8de4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_exists_first_zero_second_nonzero
import Theorems.Thm_QEC_Coding_BDL26RXFaceSecondReadout_nonzero_second_returned
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_base_history_spec
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_original_correction_equation
import Theorems.Thm_QEC_Coding_BDL26FirstZeroFaceEndpoint_original_correction_equation
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_base_history_spec
import Theorems.Thm_QEC_Coding_BDL26FirstZeroQVertexTower_original_correction_equation
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_base_history_spec
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_full_potential_formula
import Theorems.Thm_QEC_Coding_BDL26RXFaceEdgeTower_original_correction_equation


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
theorem _root_.solution :
    ∃ (S : OddScale) (n : Nat) (u : XSyndromeDomain S n) (q : Physical S (n+2))
      (t : BDL26RXFaceEdgeTower.Tower S n q)
      (w : Word F (BDL26LevelTwoDecoder.ExecutableQ S)),
      firstReadout S n u=0 ∧ secondReadout S n u q≠0 ∧
      BDL26LevelTwoLocalBranchEndpoint.localSearch S (secondReadout S n u q)=some w ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)=BDL26LevelTwoDecoder.toActualError S w ∧
      levelTwoLocalError S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q)) ∧
      BDL26RXFaceEdgeTower.delta S (BDL26RXFaceEdgeTower.D S (secondReadout S n u q))=
        secondReadout S n u q ∧
      BDL26RXFaceEdgeTower.D S (secondReadout S n u q)≠0 ∧
      (SuffixData S n).family.coboundary0 0 (BDL26RXFaceEdgeTower.basePotential S n u q t)=
        (descent S n u q).word+
          (actualBase S n).decode (actualInputs S n (input S n u) 0)+
          (actualBase S n).decode
            (actualInputs S n (perturbTop S n (input S n u) (BDL26ActualFailureReadout.flip S n q)) 0) ∧
      BDL26RXFaceEdgeTower.fullPotential S n u q t=
        intervalMap0 (SuffixData S n) 0 (TopIndex n) (Nat.zero_le _)
          (BDL26RXFaceEdgeTower.basePotential S n u q t)+accumulated S n u q ∧
      (SuffixData S n).family.coboundary0 (TopIndex n)
        (BDL26RXFaceEdgeTower.fullPotential S n u q t)=
        BDL26ActualFailureReadout.flip S n q+xCorrection S n u+xCorrection S n (translateX S n u (BDL26ActualFailureReadout.flip S n q)) := by
  obtain ⟨S,n,u,q,⟨t⟩,hfirst,hsecond⟩ := exists_first_zero_second_nonzero
  obtain ⟨w,hw,he,hl,hd,hn⟩ := nonzero_second_returned S n u q t hfirst hsecond
  exact ⟨S,n,u,q,t,w,hfirst,hsecond,hw,he,hl,hd,hn,
    BDL26RXFaceEdgeTower.base_history_spec S n u q t hfirst,
    BDL26RXFaceEdgeTower.full_potential_formula S n u q t,
    BDL26RXFaceEdgeTower.original_correction_equation S n u q t hfirst⟩
end QEC.Coding.BDL26RXFaceSecondReadout
