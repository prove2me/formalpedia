-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.ck_Rw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:05.04291+00:00
-- url     : https://prove2.me/submissions/a29c405f-f091-459b-9258-a6628ee66a79

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {k r m : ℕ} {F : Mat k r → E} (hF : CkOn (m : ℕ∞) (GV k r) F) {v : List (Mat k r)}
    (hv : ∀ X ∈ v, inLie k r X) (n : ℕ) (hn : n + v.length ≤ m) : CkOn (n : ℕ∞) (GV k r) (Rw v F) := by
  rw [← Dw_wR]
  apply CkOn_Dw (fun x hx => by obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx; exact hv X hX)
  simp only [wR, List.length_map]
  exact sCkOn_mono (by exact_mod_cast hn) hF
end PI.UnitaryGroupMassFormula.UsCompose
