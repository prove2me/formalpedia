-- Prove2me | solution 1 for PI.WGB.FiltB_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:51.180595+00:00
-- url     : https://prove2.me/submissions/c15af2a3-c534-4f20-aa16-625ea28ce8d2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_RowActDiagMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_DetPowUnitriB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGB
open Formalism.BasicNotions MvPolynomial
namespace PI.WGB
theorem _root_.solution {σ : Type*} (ψ : σ → ℕ) {d d' : ℕ} {p q : MvPolynomial σ ℂ} (hp : p ∈ FiltB ψ d)
    (hq : q ∈ FiltB ψ d') : p * q ∈ FiltB ψ (d + d') := by
  classical
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul p q he)
  rw [map_add]
  exact Nat.add_le_add (hp a ha) (hq b hb)
end PI.WGB
