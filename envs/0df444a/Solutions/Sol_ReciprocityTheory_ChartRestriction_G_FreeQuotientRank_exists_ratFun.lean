-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_ratFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:34:07.63099+00:00
-- url     : https://prove2.me/submissions/f5fa92c2-3b8c-40e7-955c-5f87cfcab430

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDimensionalBaseSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open TensorProduct
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
theorem _root_.solution {c : Module.Dual Ω (Ω ⊗[K] V)} {K₁ : IntermediateField K Ω}
    (h : DefinedOver c K₁) :
    ∃ φ : Module.Dual K₁ (K₁ ⊗[K] V), ∀ x, algebraMap K₁ Ω (φ x) = c (inclT K₁ V x) := by
  let ψ : K₁ ⊗[K] V →ₗ[K₁] Ω := (c.restrictScalars K₁).comp (inclT K₁ V)
  have hr : ∀ x, ψ x ∈ LinearMap.range (Algebra.linearMap K₁ Ω) := fun x => by
    obtain ⟨y, hy⟩ := h x; exact ⟨y, hy⟩
  let e := LinearEquiv.ofInjective (Algebra.linearMap K₁ Ω) (algebraMap K₁ Ω).injective
  refine ⟨e.symm.toLinearMap ∘ₗ ψ.codRestrict _ hr, fun x => ?_⟩
  have h1 : ((e (e.symm ⟨ψ x, hr x⟩) : LinearMap.range (Algebra.linearMap K₁ Ω)) : Ω) = ψ x := by
    rw [e.apply_symm_apply]
  exact h1
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
