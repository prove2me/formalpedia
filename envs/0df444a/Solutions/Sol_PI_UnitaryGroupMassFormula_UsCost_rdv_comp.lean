-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.rdv_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:28:44.25934+00:00
-- url     : https://prove2.me/submissions/f7e15340-7f09-4693-a8de-3792682b70c3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_conj_letter

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
theorem _root_.solution (hR : SliceRight) (H : B.Mat k (p + s + ρ) → E) (Y : B.Mat k ρ) :
    RdV Y (fun γ' => H (gaXi k ρ σ d ξ Z γ')) =
      fun γ' => RdV (cj k (p + s) ρ ξ.1.2 Y) H (gaXi k ρ σ d ξ Z γ') := by
  funext γ'
  simp only [RdV]
  congr 1
  funext t
  rw [hR k p s ρ σ d ξ Z γ' _, conj_letter]
end PI.UnitaryGroupMassFormula.UsCost
