-- Prove2me | solution 1 for PI.PolynomialProperness.mulVec_fmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:22.139326+00:00
-- url     : https://prove2.me/submissions/7cfddaef-ec43-4a70-a2de-fcd0d51def7f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
namespace PI.PolynomialProperness
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (b : Fin (r + 1)) :
    g *ᵥ fmul k r z c b = ∑ a, c a b • (g *ᵥ fvec k r z a) := by
  unfold fmul
  rw [← mulVecLin_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, mulVecLin_apply]
end PI.PolynomialProperness
