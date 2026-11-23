-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lowWord_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:58.344798+00:00
-- url     : https://prove2.me/submissions/4c46974f-39bc-4685-9e8d-fea725e5656e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : ∀ a, E a a y = (μ a : ℂ) • y) :
    ∀ (l : List (Fin n × Fin n)) (a : Fin n),
      E a a (lowWord E y l) = (lowWt μ l a : ℂ) • lowWord E y l
  | [], a => by simpa [lowWord, lowWt] using hy a
  | p :: l, a => by
    obtain ⟨c, d⟩ := p
    have h := congrArg (fun X : Module.End ℂ M => X (lowWord E y l)) (hE a a c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [solution hE hy l a, map_smul, sub_eq_iff_eq_add] at h
    simp only [lowWord, lowWt]
    rw [h]
    simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    by_cases hac : a = c <;> by_cases had : a = d
    · subst hac; subst had; simp
    · subst hac
      simp only [if_neg had, if_neg (Ne.symm had), LinearMap.zero_apply, sub_zero]
      push_cast
      module
    · subst had
      simp only [if_neg hac, LinearMap.zero_apply, zero_sub]
      push_cast
      module
    · simp [hac, had, Ne.symm had]
end ReciprocityTheory.ChartRestriction.DS
