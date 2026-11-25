-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lowWord_raise
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:38:39.431845+00:00
-- url     : https://prove2.me/submissions/ae7ca2f8-2490-4e47-bc56-1f6bb6435d70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kLowSpan_low_stable
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowWord_mem_of_ge

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
theorem _root_.solution (hE : IsGlRep E) {μ : Fin n → ℝ} {y : M} (hy : IsKHWVec ε E μ y) :
    ∀ (l : List (Fin n × Fin n)), (∀ p ∈ l, IsKLow ε p) → ∀ a b : Fin n, a < b → ε a = ε b →
      E a b (lowWord E y l) ∈ kLowSpan ε E y
  | [], _, a, b, hab, hε => by
    simp only [lowWord]
    rw [hy.2 a b hab hε]
    exact Submodule.zero_mem _
  | p :: l, hl, a, b, hab, hε => by
    obtain ⟨c, d⟩ := p
    have hcd : IsKLow ε (c, d) := hl _ (List.mem_cons_self ..)
    have hl' : ∀ p ∈ l, IsKLow ε p := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have ih := solution hE hy l hl'
    have key : ∀ a' b' : Fin n, ε a' = ε b' → E a' b' (lowWord E y l) ∈ kLowSpan ε E y := by
      intro a' b' h'
      rcases lt_or_ge a' b' with h | h
      · exact ih a' b' h h'
      · exact lowWord_mem_of_ge hE hy.1 hl' h h'
    have h := congrArg (fun X : Module.End ℂ M => X (lowWord E y l)) (hE a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [sub_eq_iff_eq_add] at h
    simp only [lowWord]
    rw [h]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (kLowSpan_low_stable hcd _ (ih a b hab hε))
    · split_ifs with hbc
      · subst hbc; exact key a d (hε.trans hcd.2)
      · simp
    · split_ifs with hda
      · subst hda; exact key c b (hcd.2.trans hε)
      · simp
end ReciprocityTheory.ChartRestriction.DS
