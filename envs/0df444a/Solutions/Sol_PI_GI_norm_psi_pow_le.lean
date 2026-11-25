-- Prove2me | solution 1 for PI.GI.norm_psi_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:41.342801+00:00
-- url     : https://prove2.me/submissions/64d74bac-9831-4b46-8ceb-d9ed5d8b6391

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaussianDualMeasure_SecondCountableTopologyAndT2Space
import Theorems.Thm_PI_GI_isCompact_mul_integer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory
noncomputable section
open PI PI.GI
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace PI.GI
theorem _root_.solution (ψ : AddChar F ℂ) (hc : Continuous ψ) (x : F) :
    ∃ C : ℝ, ∀ n : ℕ, ‖ψ x‖ ^ n ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_mul_integer x).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun n => ?_⟩
  have hmem : (n • x) ∈ (fun u => x * u) '' (𝒪[F] : Set F) :=
    ⟨(n : F), natCast_mem _ n, by simp [nsmul_eq_mul, mul_comm]⟩
  have := hC _ hmem
  rwa [AddChar.map_nsmul_eq_pow, norm_pow] at this
end PI.GI
