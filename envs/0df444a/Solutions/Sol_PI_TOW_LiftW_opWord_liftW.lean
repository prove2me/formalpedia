-- Prove2me | solution 1 for PI.TOW.LiftW.opWord_liftW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:41.007209+00:00
-- url     : https://prove2.me/submissions/3a28428b-b991-48fa-bd68-297ecb80985a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS
import Theorems.Thm_PI_TOW_LiftW_pderiv_embS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW PI.TOW.LiftW
open PI.TO PI.TOW
variable {K : Type} [CommRing K] {n' k : ℕ}
namespace PI.TOW.LiftW
theorem _root_.solution (t : Fin n') (l : List (Fin k × Fin k)) (F : MvPolynomial (Fin k) K)
    (R : MvPolynomial (Fin n' × Fin k) K) (hR : ∀ b, pderiv (t, b) R = 0) :
    opWord (liftW t l) (embS K t F * R) = embS K t (word1 l F) * R := by
  induction l with
  | nil => simp [opWord, liftW, word1]
  | cons y l ih =>
    have e1 : opWord (liftW t (y :: l)) (embS K t F * R)
        = X (t, y.1) * pderiv (t, y.2) (opWord (liftW t l) (embS K t F * R)) := by
      simp [opWord, liftW]
    have e2 : word1 (y :: l) F = X y.1 * pderiv y.2 (word1 l F) := by
      simp [word1]
    rw [e1, ih, e2, Derivation.leibniz, hR, pderiv_embS]
    simp [embS, map_mul, rename_X]
    ring
end PI.TOW.LiftW
