-- Prove2me | solution 1 for PI.FJMP.rightRootOperator_eq_signedPolarization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:39.40781+00:00
-- url     : https://prove2.me/submissions/d23f7327-37d2-4776-9530-a14c623f296b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
namespace PI.FJMP
theorem _root_.solution {p q r s : ℕ} (c d : Ix r s) (hcd : c ≠ d)
    (hsame : ∀ a : Ix p q, linePos ((a, d) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) (P : Pol p q r s) :
    rai2 (p := p) (q := q) c d P = gR (fun a : Ix p q => ((a, c) : Ln p q r s)) (fun a => (a, d))
      (fun a => linePos ((a, c) : Ln p q r s)) P := by
  unfold rai2 gR
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  show raiB (a, c) (lowB (a, d) P) = _
  beta_reduce
  unfold raiB lowB
  rw [hsame a]
  by_cases h : linePos ((a, c) : Ln p q r s) = true
  · simp only [if_pos h]
    simp
  · have hne : ((a, d) : Ln p q r s) ≠ (a, c) := fun e => hcd (Prod.ext_iff.mp e).2.symm
    simp only [if_neg h]
    simp [Derivation.leibniz, pderiv_X_of_ne hne, hne]
end PI.FJMP
