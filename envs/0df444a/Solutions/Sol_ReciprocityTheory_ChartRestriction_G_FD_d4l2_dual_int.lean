-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.d4l2_dual_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:50.681913+00:00
-- url     : https://prove2.me/submissions/a3bf0124-5cd4-4ea8-af2f-c718ea977d4d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (t : E) (h : ∀ γ : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (t * γ) = k) :
    IsIntegral ℤ ((NumberField.discr E : E) * t) := by
  classical
  have ht : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨γ, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨k, hk⟩ := h γ
    refine RingHom.mem_range.2 ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hk.symm
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := fun i => by
    rw [NumberField.integralBasis_apply]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  have key := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 ht
  have e : Algebra.discr ℚ (NumberField.integralBasis E) • (1 : E) * t =
      (NumberField.discr E : E) * t := by
    rw [← NumberField.coe_discr, Algebra.smul_def, mul_one]
    simp
  rwa [e] at key
end ReciprocityTheory.ChartRestriction.G.FD
