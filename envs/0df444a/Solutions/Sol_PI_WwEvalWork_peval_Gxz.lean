-- Prove2me | solution 1 for PI.WwEvalWork.peval_Gxz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:14:41.543725+00:00
-- url     : https://prove2.me/submissions/da008039-3752-4a6f-9ee4-7c24327bd93b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwEvalWork
open MvPolynomial
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {l : ℕ} [Fact l.Prime] {N0 N1 : ℕ}
namespace PI.WwEvalWork
theorem _root_.solution (x : Lt × ℕ × Fin N0 → ℂ_[l]) (nu : Lt → YoungDiagram)
    (I : PI.WwEval.KM.ColChoice N1 nu) :
    peval x (PI.WwEval.KM.Gxz N0 N1 nu I) =
      MvPolynomial.aeval (fun v : Lt × ℕ × Fin N1 => ∑ a : Fin N0,
          MvPolynomial.C (x (v.1, v.2.1, a)) * MvPolynomial.X ((v.1, a, v.2.2) : Lt × Fin N0 × Fin N1))
        (PI.WwEval.KM.nablaX N1 nu I) := by
  unfold PI.WwEval.KM.Gxz PI.WwEval.KM.nablaX PI.WwEval.KM.minorXZ
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, AlgHom.map_det]
  congr 1
  ext i k
  simp [peval, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply]
end PI.WwEvalWork
