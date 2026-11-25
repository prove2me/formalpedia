-- Prove2me | solution 1 for PI.TOW.blockSubstitution_blockInclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:35.691882+00:00
-- url     : https://prove2.me/submissions/0f55dcea-fdf8-4b1c-87df-1d01ab5cb93c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin

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
open PI PI.TOW
open PI.TO
namespace PI.TOW
theorem _root_.solution {K : Type} [CommRing K] {n' m : ℕ} (vec : Fin n' → Bool) (t : Fin n')
    (P : MvPolynomial (Fin (m + 1)) K) :
    Th0 K m vec (embS K t P) = blockEmb K t (theta K m (vec t) P) := by
  have hc : (Th0 K m vec).comp (embS K t) = (blockEmb K t).comp (theta K m (vec t)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [Th0, embS, theta, blockEmb]
  exact AlgHom.congr_fun hc P
end PI.TOW
