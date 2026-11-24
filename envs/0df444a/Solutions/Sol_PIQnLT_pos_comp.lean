-- Prove2me | solution 1 for PIQnLT.pos_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:24:20.704491+00:00
-- url     : https://prove2.me/submissions/54b82add-806b-4fce-a80f-b8a9cc7cd279

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_LzConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelTransfer_SecondCapelliMinorLevel

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
omit hL
namespace PIQnLT
theorem _root_.solution {t : ℕ} (pos₁ : Fin t → Fin (2 * (i + r') + k + 1)) (pos₂ : Fin t → Fin (2 * r' + k + 1))
    (hpos : ∀ j, pos₁ j = levPos k i r' (pos₂ (Fin.cast rfl j))) : pos₁ = levPos k i r' ∘ pos₂ := by
  funext j
  exact hpos j
end PIQnLT
