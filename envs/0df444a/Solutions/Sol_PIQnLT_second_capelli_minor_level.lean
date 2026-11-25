-- Prove2me | solution 1 for PIQnLT.second_capelli_minor_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:56.822477+00:00
-- url     : https://prove2.me/submissions/70f10aa4-522e-407a-bd34-8d641fa1439e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
import Theorems.Thm_PIQnLT_qminorOp_lev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PIQnLT
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k i r' : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (hL : LevHom)
include hL
namespace PIQnLT
theorem _root_.solution {t : ℕ} (pos : Fin t → Fin (2 * r' + k + 1)) (u : ℂ)
    (a a₁ β β₁ : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → Fin t → ℂ)
    (a' a₁' β' β₁' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ → Fin t → ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (ha : a (ιLev k i r' x) = a' x) (ha₁ : a₁ (ιLev k i r' x) = a₁' x)
    (hb : β (ιLev k i r' x) = β' x) (hb₁ : β₁ (ιLev k i r' x) = β₁' x) :
    chat2L (Formalism.FourierDecayAlt.Q.EH k (i + r')) (levPos k i r' ∘ pos) u a a₁ β β₁ F (ιLev k i r' x) =
      chat2L (Formalism.FourierDecayAlt.Q.EH k r') pos u a' a₁' β' β₁' (fun y => F (ιLev k i r' y)) x := by
  simp only [chat2L]
  rw [ha, ha₁, hb, hb₁]
  refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ =>
    Finset.sum_congr rfl fun j₃ _ => Finset.sum_congr rfl fun j₄ _ => ?_
  split_ifs
  · rw [Function.comp_assoc, Function.comp_assoc, qminorOp_lev]
    all_goals try exact hL
  · rfl
end PIQnLT
