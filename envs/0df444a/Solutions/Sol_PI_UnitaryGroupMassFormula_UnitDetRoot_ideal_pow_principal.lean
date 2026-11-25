-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.ideal_pow_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:19.681379+00:00
-- url     : https://prove2.me/submissions/af29a20c-b7da-48e2-b30d-52d5bbd813f7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NormLeOneOfRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal

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
theorem _root_.solution (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ I ^ hF F = span (𝓞 F) {a} := by
  have hI' : I ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  have hIh : I ^ hF F ∈ (Ideal (𝓞 F))⁰ := pow_mem hI' _
  have h1 : ClassGroup.mk0 ⟨I ^ hF F, hIh⟩ = 1 := by
    have e : (⟨I ^ hF F, hIh⟩ : (Ideal (𝓞 F))⁰) = ⟨I, hI'⟩ ^ hF F := Subtype.ext (by simp)
    rw [e, map_pow, pow_card_eq_one]
  rw [ClassGroup.mk0_eq_one_iff] at h1
  obtain ⟨⟨a, ha⟩⟩ := h1
  refine ⟨a, ?_, ha⟩
  rintro rfl
  have h0 : I ^ hF F = 0 := by rw [ha]; simp
  exact zero_notMem_nonZeroDivisors (h0 ▸ hIh)
end PI.UnitaryGroupMassFormula.UnitDetRoot
