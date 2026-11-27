-- Prove2me | solution 1 for UpperTheory.V.isCompField_ofChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:57.792347+00:00
-- url     : https://prove2.me/submissions/8b5f97c0-2ed2-436f-b6ad-d38469cbd41c

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
import Theorems.Thm_UpperTheory_V_AbF_ker_ofChar
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Polynomial
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top
namespace UpperTheory.V
theorem _root_.solution (ψ : PChar) (e q d : ℕ) (E : Type) [Field E] [NumberField E] :
    IsCompField (AbF.ofChar ψ) e q d E ↔ IsChiField ψ e q d E := by
  simp only [IsCompField, IsChiField, AbF.ker_ofChar]
  rfl
end UpperTheory.V
