-- Prove2me | solution 1 for PI.LocFramePrimWork.Assemble_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:49:52.364043+00:00
-- url     : https://prove2.me/submissions/b45b5bb9-601e-4772-a455-650b0a002a51

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
namespace PI.LocFramePrimWork
theorem _root_.solution {r : ℕ} (a : Fin r) :
    (-((r : ℤ) - ((a : ℕ) : ℤ))) = -(((r - (a : ℕ) : ℕ)) : ℤ) := by
  rw [Nat.cast_sub a.isLt.le]
end PI.LocFramePrimWork
