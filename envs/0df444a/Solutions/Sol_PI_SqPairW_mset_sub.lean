-- Prove2me | solution 1 for PI.SqPairW.mset_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:17.381962+00:00
-- url     : https://prove2.me/submissions/e91c963d-9706-405b-a696-ea3ae430ab17

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
theorem _root_.solution {R : Subring (Matrix (Fin N) (Fin N) E)} (hstar : ∀ x ∈ R, xᴴ ∈ R)
    {e : Matrix (Fin N) (Fin N) E} (he : e ∈ R) : ∀ M ∈ mset e, M ∈ R := by
  have h1e : 1 - e ∈ R := R.sub_mem R.one_mem he
  rintro M (rfl | rfl | rfl)
  · exact R.sub_mem (R.mul_mem he he) he
  · exact R.mul_mem (hstar e he) he
  · exact R.mul_mem (hstar _ h1e) h1e
end PI.SqPairW
