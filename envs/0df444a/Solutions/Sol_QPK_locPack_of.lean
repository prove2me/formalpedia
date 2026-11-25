-- Prove2me | solution 1 for QPK.locPack_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:19:10.039663+00:00
-- url     : https://prove2.me/submissions/209068e0-c63f-4573-8daf-e0ab68ff7ccb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_ProdSetIsClosed
import Theorems.Thm_QPK_prodSet_isClosed
import Theorems.Thm_QPK_prodSet_isGrp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Pointwise
open QPK
namespace QPK
theorem _root_.solution (hE : HaarExist) (hC : ConjInv) (hS : SMeas) (hB : Bruhat) (hW : LocWeil) :
    LocPack := by
  intro G _ _ _ _ _ _ _ _ muG _ N H hN hH gN gH hnorm hR
  obtain ⟨μN, hNinv, hNf, hNpos⟩ := hE G N hN gN
  obtain ⟨μH, hHinv, hHf, hHpos⟩ := hE G H hH.isClosed gH
  have hconj := hC G N H hN hH gN gH hnorm μN hNinv hNf hNpos
  obtain ⟨hPinv, hPf, hPpos, hPright, hPinvol⟩ :=
    hS G N H hN hH gN gH hnorm hR μN μH hNinv hNf hNpos hHinv hHf hHpos hconj
  obtain ⟨β, hβm, hβ⟩ := hB G (prodSet N H) (prodSet_isClosed hN hH) (prodSet_isGrp gN gH hnorm)
    (mulMap μN μH) hPinv hPf hPpos hPright
  refine ⟨μN, μH, β, hNinv, hHinv, hPinv, hβm, hβ, ?_⟩
  intro F hF
  haveI := hPf
  have hsf : SigmaFinite (mulMap μN μH) := by
    first
      | exact inferInstance
      | exact MeasureTheory.sigmaFinite_of_isFiniteMeasureOnCompacts _
  exact hW G muG (mulMap μN μH) hsf hPinvol β hβm hβ F hF
end QPK
