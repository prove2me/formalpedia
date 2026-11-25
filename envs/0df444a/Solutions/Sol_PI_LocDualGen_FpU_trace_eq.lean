-- Prove2me | solution 1 for PI.LocDualGen.FpU.trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:51:01.166256+00:00
-- url     : https://prove2.me/submissions/910ff762-c6da-42ac-9489-d9b232cf8214

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator
import Theorems.Thm_PI_LocDualGen_FpU_B_apply
import Theorems.Thm_PI_LocDualGen_FpU_repr_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsLocalRing
open PI PI.LocDualGen PI.LocDualGen.FpU
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
variable [CharP 𝓀[K] l]
attribute [local instance] algRes
namespace PI.LocDualGen.FpU
theorem _root_.solution (hcont : Continuous (algebraMap ℚ_[l] K)) (huni : Irreducible ((l : ℕ) : 𝒪[K]))
    (x : 𝒪[K]) : Algebra.trace ℚ_[l] K (x : K) =
      ((∑ i, coef K l hcont huni (x * blift K l i) i : ℤ_[l]) : ℚ_[l]) := by
  rw [Algebra.trace_eq_matrix_trace (B K l hcont huni), Matrix.trace]
  rw [show ((∑ i, coef K l hcont huni (x * blift K l i) i : ℤ_[l]) : ℚ_[l]) =
      ∑ i, ((coef K l hcont huni (x * blift K l i) i : ℤ_[l]) : ℚ_[l]) from
    map_sum PadicInt.Coe.ringHom _ _]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, B_apply]
  have e : (x : K) * (blift K l i : K) = ((x * blift K l i : 𝒪[K]) : K) := rfl
  rw [e, repr_coe]
end PI.LocDualGen.FpU
