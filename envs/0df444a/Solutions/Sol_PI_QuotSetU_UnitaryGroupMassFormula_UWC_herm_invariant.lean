-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.UWC.herm_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:18.56288+00:00
-- url     : https://prove2.me/submissions/6659c614-e2d4-4fd4-b632-3035085adfff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact

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
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.UWC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.UWC
theorem _root_.solution {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) :
    star (h *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ (h *ᵥ v)) = star u ⬝ᵥ (Hpk k r *ᵥ v) := by
  have hh' : hᴴ * (Hpk k r * h) = Hpk k r := by rw [← Matrix.mul_assoc]; exact hh
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, hh']
end PI.QuotSetU.UnitaryGroupMassFormula.UWC
