-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_listSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:24.743889+00:00
-- url     : https://prove2.me/submissions/5139443a-ad2f-4bc6-8575-d0cfef0bad38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand

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
theorem _root_.solution {α : Type*} (L : List α) (f : α → ℝ → E) (f' : α → E)
    (h : ∀ a ∈ L, HasDerivAt (f a) (f' a) 0) :
    HasDerivAt (fun t => (L.map fun a => f a t).sum) (L.map f').sum 0 := by
  induction L with
  | nil => simpa using hasDerivAt_const (0 : ℝ) (0 : E)
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun b hb => h b (List.mem_cons_of_mem _ hb))
end PI.UnitaryGroupMassFormula.UsCompose
