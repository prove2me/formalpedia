-- Prove2me | solution 1 for UnipMove.sDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:26.002513+00:00
-- url     : https://prove2.me/submissions/bb62e60c-9b68-43a3-8767-5c3691443bd5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_SDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace UnipMove
theorem _root_.solution : SDual E := by
  intro t ht
  have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := by
    intro i
    rw [NumberField.integralBasis_apply]
    exact (NumberField.RingOfIntegers.basis E i).isIntegral_coe
  have hx : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨k, hk⟩ := ht y
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    rw [show algebraMap (𝓞 E) E y = (y : E) from rfl, hk]
    simp
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hI := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 hx
  rw [← NumberField.coe_discr, Algebra.smul_def, mul_one, map_intCast] at hI
  let α : 𝓞 E := ⟨_, hI⟩
  have hα : (α : E) = (NumberField.discr E : E) * t := rfl
  rcases Int.natAbs_eq (NumberField.discr E) with h | h
  · refine ⟨α, ?_⟩
    have h' : ((NumberField.discr E : ℤ) : E) = (((NumberField.discr E).natAbs : ℤ) : E) :=
      congrArg _ h
    rw [hα, h', Int.cast_natCast]
  · refine ⟨-α, ?_⟩
    have h' : ((NumberField.discr E : ℤ) : E) = ((-((NumberField.discr E).natAbs : ℤ) : ℤ) : E) :=
      congrArg _ h
    show -(α : E) = _
    rw [hα, h', Int.cast_neg, Int.cast_natCast]
    ring
end UnipMove
