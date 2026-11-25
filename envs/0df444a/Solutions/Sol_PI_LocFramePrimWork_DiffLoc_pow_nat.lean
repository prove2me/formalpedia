-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_pow_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:57.088019+00:00
-- url     : https://prove2.me/submissions/05fdf6aa-85c4-4402-94f5-e0b890676f62

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_psi_mul
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_psi_one
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_PP
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_psi_ddE

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
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution (k : ℕ) :
    DiffLoc_psi v (((ddE (E := E) F) ^ k : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
      Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k * DiffLoc_P (E := E) v := by
  induction k with
  | zero => rw [pow_zero, DiffLoc_psi_one, pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ, DiffLoc_psi_mul, ih, DiffLoc_psi_ddE, pow_succ]
    calc _ = Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k *
          Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} *
          (DiffLoc_P (E := E) v * DiffLoc_P (E := E) v) := by ring
      _ = _ := by rw [DiffLoc_PP]
end PI.LocFramePrimWork
