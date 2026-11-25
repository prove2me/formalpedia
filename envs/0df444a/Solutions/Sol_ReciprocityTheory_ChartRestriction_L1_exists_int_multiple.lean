-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.exists_int_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:36:23.78585+00:00
-- url     : https://prove2.me/submissions/19a6a95c-53b7-48cb-874c-73f2468502dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModSepInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {Ω : Type*} [Field Ω] [CharZero Ω] {β : Ω} (hβ : IsIntegral ℤ β) (h0 : β ≠ 0) :
    ∃ (n : ℤ) (γ : Ω), n ≠ 0 ∧ IsIntegral ℤ γ ∧ (n : Ω) = β * γ := by
  obtain ⟨p, hpm, hp0⟩ := id hβ
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  have haq : Polynomial.aeval β q = 0 := by
    have h1 : Polynomial.aeval β p = 0 := by rw [Polynomial.aeval_def]; exact hp0
    rw [hpq, map_mul, map_pow, Polynomial.aeval_X] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ h0)
  refine ⟨q.coeff 0, -(Polynomial.aeval β q.divX), hq0, ?_, ?_⟩
  · have hmem := adjoin_le_integralClosure hβ (Polynomial.aeval_mem_adjoin_singleton ℤ β (p := q.divX))
    exact (neg_mem hmem : _ ∈ integralClosure ℤ Ω)
  · have h2 := congrArg (Polynomial.aeval β) (Polynomial.divX_mul_X_add q)
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, haq, eq_intCast] at h2
    linear_combination h2
end ReciprocityTheory.ChartRestriction.L1
