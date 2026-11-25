-- Prove2me | solution 1 for P2M_Formalism_FG_SolveVAux_low_pow_sub__02c94c820c08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:36:36.06439+00:00
-- url     : https://prove2.me/submissions/f0cc09ee-3e9d-4090-80bb-09c83ba503f7

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Theorems.Thm_Formalism_FG_SolveVAux_low_of_zero
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul_sub
import Theorems.Thm_Formalism_FG_SolveVAux_P_add
import Theorems.Thm_Formalism_FG_SolveVAux_P_single
import Theorems.Thm_Formalism_FG_SolveVAux_P_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}
namespace Formalism.FG.SolveVAux
theorem _root_.solution {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hkk : ∀ i, Low M (k i - k' i))
    (e : ι →₀ ℕ) : Low M (P k e - P k' e) := by
  induction e using Finsupp.induction_linear with
  | zero => rw [P_zero, P_zero, sub_self]; exact low_of_zero _
  | add e₁ e₂ h₁ h₂ =>
    rw [P_add, P_add]; exact low_mul_sub h₁ h₂
  | single i n =>
    rw [P_single, P_single]
    induction n with
    | zero => rw [pow_zero, pow_zero, sub_self]; exact low_of_zero _
    | succ n ih => rw [pow_succ, pow_succ]; exact low_mul_sub ih (hkk i)
end Formalism.FG.SolveVAux
