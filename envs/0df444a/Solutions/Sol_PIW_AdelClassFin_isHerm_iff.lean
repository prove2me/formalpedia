-- Prove2me | solution 1 for PIW.AdelClassFin.isHerm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:43.881674+00:00
-- url     : https://prove2.me/submissions/3e52aea0-5793-480d-b06a-e6792e597130

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSingleLeft
import Theorems.Thm_PIW_AdelClassFin_cT_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.UG
open scoped Matrix
variable {E : Type} [Field E] [StarRing E]
namespace PIW.AdelClassFin
theorem _root_.solution {n : Type} (J : Matrix n n E) : IsHerm (starRingEnd E) J ↔ Jᴴ = J := by
  unfold IsHerm
  rw [cT_star]
end PIW.AdelClassFin
