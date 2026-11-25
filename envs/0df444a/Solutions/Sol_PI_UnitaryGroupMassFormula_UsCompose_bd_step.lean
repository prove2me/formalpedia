-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.bd_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:55:32.566731+00:00
-- url     : https://prove2.me/submissions/062fc096-7ae9-4467-aecb-7f1a06f1354e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_cmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution (hP : DegDP) (hD : DegD) {k j ρ κ ℓ : ℕ} {X : Mat k (j + ρ)} (hX : inLie k (j + ρ) X)
    {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) : Bd k j ρ (κ + j) (ℓ + 1) (step k j ρ X L) := by
  intro e he
  rw [step, List.mem_flatMap] at he
  obtain ⟨e₀, he₀, hmem⟩ := he
  obtain ⟨hdeg, hlen, hlie⟩ := h e₀ he₀
  simp only [stepOne, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact ⟨(hP _ _ _).trans (hdeg.trans (Nat.le_add_right _ _)), hlen.trans (Nat.le_succ _), hlie⟩
  · exact ⟨(deg_cmul _ _ _).trans (Nat.add_le_add hdeg ((hP _ _ _).trans (hD k j ρ).1)),
      hlen.trans (Nat.le_succ _), hlie⟩
  · exact ⟨(deg_cmul _ _ _).trans (Nat.add_le_add hdeg ((hP _ _ _).trans (hD k j ρ).2)),
      hlen.trans (Nat.le_succ _), hlie⟩
  · refine ⟨hdeg.trans (Nat.le_add_right _ _), by simpa using hlen, ?_⟩
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    · exact hX
    · exact hlie Y hY
end PI.UnitaryGroupMassFormula.UsCompose
