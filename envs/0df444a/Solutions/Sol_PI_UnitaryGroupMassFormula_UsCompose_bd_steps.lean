-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.bd_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:06:32.509928+00:00
-- url     : https://prove2.me/submissions/63eaaf29-bdb2-4f93-bbe1-b485285a3c29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_Bd_mono
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_bd_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono


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
theorem _root_.solution (hP : DegDP) (hD : DegD) {k j ρ κ ℓ : ℕ} {w : List (Mat k (j + ρ))}
    (hw : ∀ X ∈ w, inLie k (j + ρ) X) {L : FS k (j + ρ)} (h : Bd k j ρ κ ℓ L) :
    Bd k j ρ (κ + j * w.length) (ℓ + w.length) (steps k j ρ w L) := by
  induction w with
  | nil => simpa [steps] using h
  | cons X w ih =>
    have h1 := bd_step hP hD (hw X (by simp)) (ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)))
    show Bd k j ρ _ _ (step k j ρ X (steps k j ρ w L))
    exact h1.mono (le_of_eq (by rw [List.length_cons]; ring)) (le_of_eq (by rw [List.length_cons]; ring))
end PI.UnitaryGroupMassFormula.UsCompose
