-- Prove2me | solution 1 for QEC.Coding.BDL26FirstZeroQVertexTower.terminal_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:21:19.014286+00:00
-- url     : https://prove2.me/submissions/1a5af113-06dd-486b-bae6-701f50f4f177

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroEmptySuffix
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_FirstZeroQVertexTower
import Theorems.Thm_QEC_Coding_BDL26FirstZeroEmptySuffix_physical_flip_local
import Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_levelTwoLocalError_iff_owner


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FirstZeroQVertexTower
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout
open scoped Classical BigOperators
namespace QEC.Coding.BDL26FirstZeroQVertexTower
theorem _root_.solution (S : OddScale) (n : Nat) (u : XSyndromeDomain S n)
    (q : Physical S (n+2)) (t : Tower S n q) :
    levelTwoLocalError S (terminalWord S n u q) := by
  rcases terminal_cases S n u q t with hz | hb
  · apply (levelTwoLocalError_iff_owner S _).mpr
    refine ⟨BDL26ReplacementSupport.rzCorrectionOwner (RawOne S) S (bottom t),?_⟩
    intro r hr
    rw [hz] at hr
    exact False.elim (hr rfl)
  · rw [hb]
    exact BDL26FirstZeroEmptySuffix.physical_flip_local S (bottom t)
end QEC.Coding.BDL26FirstZeroQVertexTower
