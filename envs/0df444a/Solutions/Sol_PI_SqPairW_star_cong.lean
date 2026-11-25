-- Prove2me | solution 1 for PI.SqPairW.star_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:26.525405+00:00
-- url     : https://prove2.me/submissions/dc35aa1c-9841-474d-9fc1-ffadf24ae52a

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
    (b + P • d)ᴴ * (b + P • d) = bᴴ * b + P • (bᴴ * d + dᴴ * b + P • (dᴴ * d)) := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_zsmul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  abel
end PI.SqPairW
