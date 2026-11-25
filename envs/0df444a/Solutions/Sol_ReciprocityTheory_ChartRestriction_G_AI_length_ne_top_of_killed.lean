-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_ne_top_of_killed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:28:02.201522+00:00
-- url     : https://prove2.me/submissions/2f3c22f6-0441-4909-893c-5cd4c90573e9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqOfSurjOfKerEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
universe u
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [Module.Finite A N] (I : Ideal A) (hI : ∀ r ∈ I, ∀ x : N, r • x = 0)
    (hfin : Module.length A (A ⧸ I) ≠ ⊤) : Module.length A N ≠ ⊤ := by
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hfin ⊢
  obtain ⟨hN, hA⟩ := hfin
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := N)
  let φ : Fin n → (A ⧸ I) →ₗ[A] N := fun i =>
    Submodule.liftQ I (LinearMap.toSpanSingleton A N (s i)) (by
      intro r hr
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hI r hr (s i))
  let Φ : (Fin n → A ⧸ I) →ₗ[A] N := ∑ i, (φ i).comp (LinearMap.proj i)
  have hΦ : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
      simp only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact ⟨isNoetherian_of_surjective Φ (LinearMap.range_eq_top.mpr hΦ),
    isArtinian_of_surjective _ Φ hΦ⟩
end ReciprocityTheory.ChartRestriction.G.AI
