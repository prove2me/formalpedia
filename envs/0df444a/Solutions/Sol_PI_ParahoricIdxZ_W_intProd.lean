-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.intProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:14.062827+00:00
-- url     : https://prove2.me/submissions/d4436764-afbc-4b10-8d95-92c3b00ad22a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
namespace PI.ParahoricIdxZ.W
theorem _root_.solution {l m n : Type} [Fintype m] {X : Matrix l m F} {Y : Matrix m n F}
    (hX : ∀ i j, X i j ∈ O) (hY : ∀ i j, Y i j ∈ O) : ∀ i j, (X * Y) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact O.sum_mem fun k _ => O.mul_mem (hX i k) (hY k j)
end PI.ParahoricIdxZ.W
