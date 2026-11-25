-- Prove2me | solution 1 for PIQnLT.capL_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:02:49.159875+00:00
-- url     : https://prove2.me/submissions/ffc3afe8-b550-4e3f-961c-267e71ac71bb

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel
import Theorems.Thm_PIQnLT_pos_comp
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
theorem _root_.solution {t₁ t₂ : ℕ} (h : t₁ = t₂) (pos₁ : Fin t₁ → Fin (2 * (i + r') + k + 1))
    (pos₂ : Fin t₂ → Fin (2 * r' + k + 1)) (hpos : ∀ j, pos₁ j = levPos k i r' (pos₂ (Fin.cast h j))) (u : ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    qminorOp (Formalism.FourierDecayAlt.Q.EH k (i + r')) pos₁ pos₁ u F (ιLev k i r' x) =
      qminorOp (Formalism.FourierDecayAlt.Q.EH k r') pos₂ pos₂ u (fun y => F (ιLev k i r' y)) x := by
  subst h
  have hp : pos₁ = levPos k i r' ∘ pos₂ := pos_comp pos₁ pos₂ hpos
  subst hp
  rw [qminorOp_lev]
  all_goals try exact hL
end PIQnLT
