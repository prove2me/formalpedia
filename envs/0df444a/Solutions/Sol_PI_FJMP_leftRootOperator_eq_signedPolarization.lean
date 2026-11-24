-- Prove2me | solution 1 for PI.FJMP.leftRootOperator_eq_signedPolarization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:40.928347+00:00
-- url     : https://prove2.me/submissions/d8806a3c-f49a-4d58-80af-65fce67eb60d

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
theorem _root_.solution {p q r s : ℕ} (a b : Ix p q) (hab : a ≠ b)
    (hsame : ∀ c : Ix r s, linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s)) (P : Pol p q r s) :
    rai1 (r := r) (s := s) a b P = gR (fun c : Ix r s => ((a, c) : Ln p q r s)) (fun c => (b, c))
      (fun c => linePos ((a, c) : Ln p q r s)) P := by
  unfold rai1 gR
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  show raiB (a, c) (lowB (b, c) P) = _
  beta_reduce
  unfold raiB lowB
  rw [hsame c]
  by_cases h : linePos ((a, c) : Ln p q r s) = true
  · simp only [if_pos h]
    simp
  · have hne : ((b, c) : Ln p q r s) ≠ (a, c) := fun e => hab (Prod.ext_iff.mp e).1.symm
    simp only [if_neg h]
    simp [Derivation.leibniz, pderiv_X_of_ne hne, hne]
end PI.FJMP
