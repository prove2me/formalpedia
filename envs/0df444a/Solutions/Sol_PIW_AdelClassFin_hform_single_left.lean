-- Prove2me | solution 1 for PIW.AdelClassFin.hform_single_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:53:30.363484+00:00
-- url     : https://prove2.me/submissions/ec767416-a550-4f41-bf9e-8c0d66142e17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
import Theorems.Thm_PIW_AdelClassFin_hform_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG
open scoped Matrix
variable {E : Type} [Field E] [StarRing E]
namespace PIW.AdelClassFin
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (J : Matrix n n E) (i : n) (y : n → E) :
    hform (starRingEnd E) J (Pi.single i 1) y = (J *ᵥ y) i := by
  have hs : star (Pi.single i (1 : E) : n → E) = Pi.single i 1 := by
    ext r
    by_cases h : r = i
    · subst h
      simp
    · simp [Pi.single_apply, h]
  rw [hform_eq, hs]
  simp
end PIW.AdelClassFin
