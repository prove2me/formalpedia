-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_sum_mul_pow_eq_one_1fdd236d5c86
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:42.393041+00:00
-- url     : https://prove2.me/submissions/63a73bc3-bdf6-49da-b609-ef2ba3a1faf7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
variable {S : Type*} [SetLike S Ω] [SubringClass S Ω]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (A : S) {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ A)
    (hc : ∀ l, c l ∈ A) (h1 : ∑ l, c l * f l = 1) (N : ℕ) :
    ∃ d : Fin k → Ω, (∀ l, d l ∈ A) ∧ ∑ l, d l * f l ^ N = 1 := by
  let f' : Fin k → A := fun l => ⟨f l, hf l⟩
  have hspan : Ideal.span (Set.range f') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have : (1 : A) = ∑ l, (⟨c l, hc l⟩ : A) * f' l := Subtype.ext (by simp [f', h1])
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have hpow := Ideal.span_pow_eq_top _ hspan N
  rw [← Set.range_comp] at hpow
  have h1' : (1 : A) ∈ Ideal.span (Set.range ((fun y => y ^ N) ∘ f')) := by
    rw [hpow]; exact Submodule.mem_top
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 h1'
  refine ⟨fun l => d l, fun l => (d l).2, ?_⟩
  have := congrArg Subtype.val hd
  simpa [f'] using this
end GroundTheory.Heights₂.Heights.Model
