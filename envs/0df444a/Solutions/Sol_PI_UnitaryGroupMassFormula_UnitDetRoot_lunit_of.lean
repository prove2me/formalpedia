-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.lunit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:55.727023+00:00
-- url     : https://prove2.me/submissions/3508a7a1-403d-48d4-be6a-0d02bffd767b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobTop
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_isIntegral_algebraMap_O

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution (F : IntermediateField ℚ ℂ) {α β u : ℂ} {k l : ℕ} (hα : α ≠ 0) (hβ : β ≠ 0) (hu : u ≠ 0)
    (hl : ¬ l ∣ k)
    (h1 : span (𝓞 F) {(k : ℂ) * α} ≤ span (𝓞 F) {u * β})
    (h2 : span (𝓞 F) {(k : ℂ) * (u * β)} ≤ span (𝓞 F) {α}) :
    IsLUnit l (α / β / u) := by
  refine ⟨div_ne_zero (div_ne_zero hα hβ) hu, k, hl, ?_, ?_⟩
  · obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.mp (h1 (Submodule.mem_span_singleton_self _))
    rw [Algebra.smul_def] at ho
    have e : (k : ℂ) * (α / β / u) = algebraMap (𝓞 F) ℂ o := by
      field_simp
      first | linear_combination ho | linear_combination -ho
    rw [e]
    exact isIntegral_algebraMap_O F o
  · obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.mp (h2 (Submodule.mem_span_singleton_self _))
    rw [Algebra.smul_def] at ho
    have e : (k : ℂ) * (α / β / u)⁻¹ = algebraMap (𝓞 F) ℂ o := by
      field_simp
      first | linear_combination ho | linear_combination -ho
    rw [e]
    exact isIntegral_algebraMap_O F o
end PI.UnitaryGroupMassFormula.UnitDetRoot
