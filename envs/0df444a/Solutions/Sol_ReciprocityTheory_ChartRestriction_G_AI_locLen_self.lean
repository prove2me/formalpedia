-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.locLen_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:54.135542+00:00
-- url     : https://prove2.me/submissions/e3358c74-2c16-4670-869d-cd945bed7785

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {N : Type v} [AddCommGroup N] [Module A N] (q : PrimeSpectrum A)
    (e : N ≃ₗ[A] A ⧸ q.asIdeal) : locLen N q = 1 := by
  have key : ∀ (n : N) (s : q.asIdeal.primeCompl), LocalizedModule.mk n s = 0 → n = 0 := by
    intro n s h
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    simp only [one_smul, smul_zero] at hu
    have h2 : (u : A) • e n = 0 := by rw [← map_smul, Submonoid.smul_def] at *; rw [hu, map_zero]
    rw [Algebra.smul_def, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact absurd (Ideal.Quotient.eq_zero_iff_mem.mp h2) u.2
    · simpa using h2
  have : IsSimpleModule (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl N) := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective]
    refine ⟨⟨LocalizedModule.mk (e.symm 1) 1, 0, fun h => ?_⟩, ?_⟩
    · have := congrArg e (key _ _ h)
      simp at this
    · intro y hy z
      induction y using LocalizedModule.induction_on with
      | h n s =>
      induction z using LocalizedModule.induction_on with
      | h n' t =>
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e n)
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e n')
      have haq : a ∉ q.asIdeal := by
        intro h
        apply hy
        have : n = 0 := e.injective (by rw [← ha, map_zero]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h)
        rw [this, LocalizedModule.zero_mk]
      refine ⟨Localization.mk (b * s) ⟨a * t, q.asIdeal.primeCompl.mul_mem haq t.2⟩, ?_⟩
      rw [LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
      refine ⟨1, e.injective ?_⟩
      simp only [one_smul, map_smul, Submonoid.smul_def, Submonoid.coe_mul, ← ha, ← hb,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
      ring
  exact Module.length_eq_one _ _
end ReciprocityTheory.ChartRestriction.G.AI
