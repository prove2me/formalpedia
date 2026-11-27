-- Prove2me | solution 1 for PI.GI.norm_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:15:42.663494+00:00
-- url     : https://prove2.me/submissions/bf1b3935-92f6-4779-8172-85f35786242d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaussianDualMeasure_SecondCountableTopologyAndT2Space
import Theorems.Thm_PI_GI_norm_psi_pow_le

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
theorem _root_.solution (ψ : AddChar F ℂ) (hc : Continuous ψ) (x : F) : ‖ψ x‖ = 1 := by
  have key : ∀ z : F, ‖ψ z‖ ≤ 1 := by
    intro z
    by_contra h
    rw [not_le] at h
    obtain ⟨C, hC⟩ := norm_psi_pow_le ψ hc z
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
    exact absurd (hC n) (not_le.mpr hn)
  have hmul : ψ x * ψ (-x) = 1 := by rw [← AddChar.map_add_eq_mul]; simp
  have h1 := key x
  have h2 := key (-x)
  have hn : ‖ψ x‖ * ‖ψ (-x)‖ = 1 := by rw [← norm_mul, hmul, norm_one]
  nlinarith [norm_nonneg (ψ x), norm_nonneg (ψ (-x))]
end PI.GI
