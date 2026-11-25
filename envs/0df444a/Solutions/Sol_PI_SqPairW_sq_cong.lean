-- Prove2me | solution 1 for PI.SqPairW.sq_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:21.436063+00:00
-- url     : https://prove2.me/submissions/482ba3f5-2a5d-4fbc-bb7c-977088bab092

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_SplitPairGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ConjTransposeMemLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairW
theorem _root_.solution (b d : Matrix (Fin N) (Fin N) E) (P : ℤ) :
    (b + P • d) * (b + P • d) - (b + P • d) = (b * b - b) + P • (b * d + d * b + P • (d * d) - d) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub,
    smul_smul]
  abel
end PI.SqPairW
