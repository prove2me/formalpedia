-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory.Good.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:30.028421+00:00
-- url     : https://prove2.me/submissions/bab83e24-0c6e-4d3f-b31b-c77ef3c2b9d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompCA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompactCurveEstimate

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
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CCA
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
namespace Good
theorem _root_.solution {n : ℕ} {w w' : List (Bool × B.Mat k r)} (h : Good k r n w) (hs : w'.Sublist w) :
    Good k r n w' := by
  obtain ⟨u, v, hu, hv, hl, rfl⟩ := h
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := List.sublist_append_iff.1 hs
  obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.1 (show r₁.Sublist (u.map (Prod.mk true)) from h1)
  obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.1 (show r₂.Sublist (v.map (Prod.mk false)) from h2)
  refine ⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX), ?_, rfl⟩
  have := hu'.length_le
  have := hv'.length_le
  omega
end Good
end PI.UnitaryCorollaryDerivatives.LatticeLocalGlobalTheory
