-- Prove2me | solution 1 for PI.EF.Loc.norm_refl_sphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:22.577694+00:00
-- url     : https://prove2.me/submissions/3fb7b2f2-3c07-433b-a357-3eb90b76de5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology ComplexConjugate
namespace PI.EF.Loc
theorem _root_.solution {s₀ ρ z : ℂ} {R : ℝ} (hR : 0 < R) (hz : z ∈ sphere s₀ R) :
    ‖refl s₀ R ρ z‖ = ‖z - ρ‖ := by
  have hw : ‖z - s₀‖ = R := by rwa [mem_sphere_iff_norm] at hz
  have hR2 : (R : ℂ) ^ 2 = (z - s₀) * conj (z - s₀) := by
    rw [mul_conj, normSq_eq_norm_sq, hw]
    push_cast
    ring
  have hk : (z - s₀) * conj (z - s₀) - conj (ρ - s₀) * (z - s₀) = (z - s₀) * conj (z - ρ) := by
    simp only [map_sub]
    ring
  unfold refl
  rw [hR2, hk, norm_div, norm_mul, Complex.norm_conj, hw, Complex.norm_real, Real.norm_of_nonneg hR.le]
  field_simp
end PI.EF.Loc
