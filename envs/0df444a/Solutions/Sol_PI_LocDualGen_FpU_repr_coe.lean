-- Prove2me | solution 1 for PI.LocDualGen.FpU.repr_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:41:55.146527+00:00
-- url     : https://prove2.me/submissions/cc0fda38-3839-4a60-abf2-1aa0728bc535

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_IsClosedO
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_UnramifiedDualGenerator
import Theorems.Thm_PI_LocDualGen_FpU_B_apply
import Theorems.Thm_PI_LocDualGen_FpU_Phi_coe
import Theorems.Thm_PI_LocDualGen_FpU_repr_sum
import Theorems.Thm_PI_LocDualGen_FpU_span


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
    (y : 𝒪[K]) (j : Fin (fdim K l)) :
    (B K l hcont huni).repr (y : K) j = (coef K l hcont huni y j : ℚ_[l]) := by
  have h' : (y : K) = ((Phi K l hcont (coef K l hcont huni y) : 𝒪[K]) : K) :=
    congrArg Subtype.val (span K l hcont huni y).choose_spec
  rw [h', Phi_coe]
  have e : ∑ i, algebraMap ℚ_[l] K ((coef K l hcont huni y i : ℤ_[l]) : ℚ_[l]) * (blift K l i : K) =
      ∑ i, ((coef K l hcont huni y i : ℤ_[l]) : ℚ_[l]) • B K l hcont huni i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [B_apply, Algebra.smul_def]
  rw [e, repr_sum]
end PI.LocDualGen.FpU
