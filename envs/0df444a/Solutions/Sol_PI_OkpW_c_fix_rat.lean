-- Prove2me | solution 1 for PI.OkpW.c_fix_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:19.175834+00:00
-- url     : https://prove2.me/submissions/2c7d23c8-1538-45cc-8aa1-de9ef9ad53c3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFixRat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW
variable {K : Type} [Field K] [NumberField K]
namespace PI.OkpW
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (c : K →+* K) (hc : ∃ x, c x ≠ x) {y : K}
    (hy : c y = y) : ∃ r : ℚ, (r : K) = y := by
  let D : K →ₗ[ℚ] K := c.toRatAlgHom.toLinearMap - LinearMap.id
  have hD : ∀ z, D z = c z - z := fun z => rfl
  have hS : LinearMap.ker D ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hc
    intro h
    have hm : x ∈ LinearMap.ker D := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hD, sub_eq_zero] at hm
    exact hx hm
  have hlt : Module.finrank ℚ (LinearMap.ker D) < 2 :=
    hK ▸ Submodule.finrank_lt hS
  have hle : (ℚ ∙ (1 : K)) ≤ LinearMap.ker D := by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, hD, map_one, sub_self]
  have heq : (ℚ ∙ (1 : K)) = LinearMap.ker D :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_singleton one_ne_zero]; omega)
  have hyS : y ∈ LinearMap.ker D := by rw [LinearMap.mem_ker, hD, hy, sub_self]
  rw [← heq, Submodule.mem_span_singleton] at hyS
  obtain ⟨r, hr⟩ := hyS
  exact ⟨r, by rw [← hr, Rat.smul_def, mul_one]⟩
end PI.OkpW
