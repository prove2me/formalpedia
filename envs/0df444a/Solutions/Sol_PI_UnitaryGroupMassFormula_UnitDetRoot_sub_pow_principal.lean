-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.sub_pow_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:49.73739+00:00
-- url     : https://prove2.me/submissions/6e5729df-1301-41b2-a86c-16bb0df4d949

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_span_single_pow
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_span_single_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_algebraMap_O_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_ideal_pow_principal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField nonZeroDivisors
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField
variable (F : IntermediateField ℚ ℂ)
variable [NumberField F]
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution (S : Submodule (𝓞 F) ℂ) (hS : S ≠ ⊥) (t : ℂ) (ht : t ≠ 0)
    (hle : S ≤ span (𝓞 F) {t}) :
    ∃ y : F, y ≠ 0 ∧ S ^ hF F = span (𝓞 F) {t ^ hF F * (y : ℂ)} := by
  set S0 := span (𝓞 F) {t⁻¹} * S with hS0def
  have hS0 : S0 ≤ LinearMap.range (Algebra.linearMap (𝓞 F) ℂ) := by
    rw [← Submodule.one_eq_range, Submodule.one_eq_span]
    calc S0 ≤ span (𝓞 F) {t⁻¹} * span (𝓞 F) {t} := mul_le_mul' le_rfl hle
      _ = span (𝓞 F) {1} := by rw [span_single_mul, inv_mul_cancel₀ ht]
  have hSS0 : S = span (𝓞 F) {t} * S0 := by
    rw [hS0def, ← mul_assoc, span_single_mul, mul_inv_cancel₀ ht, ← Submodule.one_eq_span, one_mul]
  set I : Ideal (𝓞 F) := Submodule.comap (Algebra.linearMap (𝓞 F) ℂ) S0 with hIdef
  have hI : Submodule.map (Algebra.linearMap (𝓞 F) ℂ) I = S0 := Submodule.map_comap_eq_of_le hS0
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hS
    rw [hSS0, ← hI, h, Submodule.map_bot, Submodule.mul_bot]
  obtain ⟨a, ha0, ha⟩ := ideal_pow_principal F I hI0
  refine ⟨algebraMap (𝓞 F) F a, ?_, ?_⟩
  · intro h
    apply ha0
    exact RingOfIntegers.ext (by simpa using h)
  have hmap : S0 ^ hF F = span (𝓞 F) {algebraMap (𝓞 F) ℂ a} := by
    have hp : Submodule.map (Algebra.linearMap (𝓞 F) ℂ) (I ^ hF F) = S0 ^ hF F := by
      rw [← hI]; exact Submodule.map_pow (M := I) (f := Algebra.ofId (𝓞 F) ℂ) (n := hF F)
    rw [← hp, ha, Submodule.map_span, Set.image_singleton]
    rfl
  rw [hSS0, mul_pow, hmap, span_single_pow, span_single_mul, algebraMap_O_apply]
end PI.UnitaryGroupMassFormula.UnitDetRoot
