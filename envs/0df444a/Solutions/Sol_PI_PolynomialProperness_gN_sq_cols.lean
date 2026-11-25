-- Prove2me | solution 1 for PI.PolynomialProperness.gN_sq_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:19.940432+00:00
-- url     : https://prove2.me/submissions/eb1760ca-423e-44c3-a7f2-b072ac342c56

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Theorems.Thm_PI_PolynomialProperness_GN_gN_sq


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
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) : B.gN g ^ 2 = ∑ j, nsq (g *ᵥ bvec j) := by
  rw [GN.gN_sq]
  have e : ∀ j i, (g *ᵥ bvec j) i = g i j := by
    intro j i
    simp [bvec, mulVec, dotProduct, Pi.single_apply]
  unfold GN.hs nsq
  simp only [e]
  exact Finset.sum_comm
end PI.PolynomialProperness
