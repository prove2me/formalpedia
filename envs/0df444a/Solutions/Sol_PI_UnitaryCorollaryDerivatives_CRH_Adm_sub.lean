-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CRH.Adm_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:36:35.34214+00:00
-- url     : https://prove2.me/submissions/5eaebaee-0d29-4cdc-989c-1f8be7b599cb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CRH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives.CRH
theorem _root_.solution {n : ℕ} {w w' : List (Bool × Mat k r)} (h : w'.Sublist w) (hw : admitted n w) : admitted n w' := by
  obtain ⟨u, v, hu, hv, hl, rfl⟩ := hw
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := List.sublist_append_iff.1 h
  obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.1 (show r₁.Sublist (u.map (Prod.mk true)) from h1)
  obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.1 (show r₂.Sublist (v.map (Prod.mk false)) from h2)
  refine ⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX), ?_, rfl⟩
  have := hu'.length_le
  have := hv'.length_le
  omega
end PI.UnitaryCorollaryDerivatives.CRH
