-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TwistedDualGensExist_exists_pow_combination_d88121157b86
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:40:42.425832+00:00
-- url     : https://prove2.me/submissions/612cc757-5189-45fd-a74e-a674534bdf7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensExist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω] {τ : Type*}
  {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TwistedDualGensExist
theorem _root_.solution (A : Subalgebra O Ω) {k : ℕ} (f cc : Fin k → Ω)
    (hf : ∀ l, f l ∈ A) (hcc : ∀ l, cc l ∈ A) (hsum : ∑ l, cc l * f l = 1) (N : ℕ) :
    ∃ g : Fin k → Ω, (∀ l, g l ∈ A) ∧ ∑ l, g l * f l ^ N = 1 := by
  set f' : Fin k → A := fun l => ⟨f l, hf l⟩ with hf'
  have h1 : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : (1 : A) = ∑ l, (⟨cc l, hcc l⟩ : A) * f' l := Subtype.ext (by simp [f', hsum])
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have h2 := Ideal.span_pow_eq_top _ h1 N
  rw [← Set.range_comp] at h2
  have h3 : (1 : A) ∈ Ideal.span (Set.range ((fun z : A => z ^ N) ∘ f')) := by
    rw [h2]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h3
  refine ⟨fun l => g l, fun l => (g l).2, ?_⟩
  have := congrArg Subtype.val hg
  simpa [f'] using this
end TwistedDualGensExist
end GroundTheory.Heights₂.Heights.NumbersDVR
