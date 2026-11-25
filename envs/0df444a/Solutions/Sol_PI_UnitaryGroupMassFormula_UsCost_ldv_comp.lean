-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ldv_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:32:31.932543+00:00
-- url     : https://prove2.me/submissions/75e07f96-f7b0-4e7a-8da7-df704bd0df4e

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
theorem _root_.solution (hL : SliceLeft) (H : B.Mat k (p + s + ρ) → E) (Y : B.Mat k ρ) :
    B.LdV Y (fun γ' => H (gaXi k ρ σ d ξ Z γ')) =
      fun γ' => B.LdV (cj k (p + s) ρ ξ.1.1 Y) H (gaXi k ρ σ d ξ Z γ') := by
  funext γ'
  simp only [B.LdV]
  congr 1
  funext t
  rw [hL k p s ρ σ d ξ Z γ' _, ← neg_smul, conj_letter, neg_smul]
end PI.UnitaryGroupMassFormula.UsCost
