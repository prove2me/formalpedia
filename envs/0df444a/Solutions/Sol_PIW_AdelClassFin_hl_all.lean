-- Prove2me | solution 1 for PIW.AdelClassFin.hl_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:15.387511+00:00
-- url     : https://prove2.me/submissions/b1d7a5e5-306f-4605-bebd-1827322734e7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
import Theorems.Thm_PIW_AdelClassFin_hl_zero
import Theorems.Thm_PIW_AdelClassFin_hl_step

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
open Formalism.UG NumberField
open scoped Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (hS : PartShort) (hU : PartUnits) (hI : PartIso) (hP : PartSplit)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (m : ℕ) : HL E m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with h0 | hm
    · subst h0
      exact hl_zero
    · exact hl_step hS hU hI hP F E hc m hm ih
end PIW.AdelClassFin
