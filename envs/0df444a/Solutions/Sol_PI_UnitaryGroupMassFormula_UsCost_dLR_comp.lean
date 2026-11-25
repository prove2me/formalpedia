-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.dLR_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:56:25.757985+00:00
-- url     : https://prove2.me/submissions/d6678f64-9112-499a-ba40-531a43d51800

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ldv_comp
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_rw_comp

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
theorem _root_.solution (hL : SliceLeft) (hR : SliceRight) (v : List (B.Mat k ρ)) (F : B.Mat k (p + s + ρ) → E) :
    ∀ u : List (B.Mat k ρ),
      B.dLR u v (fun γ' => F (gaXi k ρ σ d ξ Z γ')) =
        fun γ' => B.dLR (u.map (cj k (p + s) ρ ξ.1.1)) (v.map (cj k (p + s) ρ ξ.1.2)) F (gaXi k ρ σ d ξ Z γ')
  | [] => by
    simp only [B.dLR, List.foldr_nil, List.map_nil]
    exact rw_comp hR v F
  | Y :: u => by
    have ih := solution hL hR v F u
    simp only [B.dLR, List.foldr_cons, List.map_cons] at ih ⊢
    rw [ih]
    exact ldv_comp hL _ Y
end PI.UnitaryGroupMassFormula.UsCost
