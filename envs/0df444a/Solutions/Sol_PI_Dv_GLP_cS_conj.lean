-- Prove2me | solution 1 for PI.Dv.GLP.cS_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:19.387512+00:00
-- url     : https://prove2.me/submissions/beff78bb-a958-450d-b4e4-50da1091ca50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution (T : GoodSet K G) (s : T.S) (h x : G) : cS T s (h * x * h⁻¹) = cS T s x := by
  have := Representation.char_conj (T.tau s) x⁻¹ h
  simp only [Representation.character] at this
  simp only [cS]
  rw [show (h * x * h⁻¹)⁻¹ = h * x⁻¹ * h⁻¹ by group, this]
end PI.Dv.GLP
