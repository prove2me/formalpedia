-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.rw_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:42.146763+00:00
-- url     : https://prove2.me/submissions/a5c2c6e6-214e-4e25-9811-e8557947f10b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_rdv_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ} {ξ : Xi k p s ρ σ} {Z : G.Mat s}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution (hR : SliceRight) :
    ∀ (v : List (B.Mat k ρ)) (F : B.Mat k (p + s + ρ) → E),
      B.Rw v (fun γ' => F (gaXi k ρ σ d ξ Z γ')) =
        fun γ' => B.Rw (v.map (cj k (p + s) ρ ξ.1.2)) F (gaXi k ρ σ d ξ Z γ')
  | [], _ => rfl
  | Y :: v, F => by
    simp only [B.Rw, List.foldr_cons, List.map_cons] at *
    have ih := solution hR v F
    simp only [B.Rw] at ih
    rw [ih]
    exact rdv_comp hR _ Y
end PI.UnitaryGroupMassFormula.UsCost
