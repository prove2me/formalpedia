-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.sum_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:32:19.886912+00:00
-- url     : https://prove2.me/submissions/37f0bdb3-a43f-4170-a9d9-4543c738c06b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_side_inl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_side_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution {M : Type} [AddCommMonoid M] (s : ι → Bool) (g : ι → ι → M)
    (hg : ∀ l l', g l l' ≠ 0 → s l = true ∧ s l' = false) :
    ∑ l, ∑ l', g l l' = ∑ i, ∑ j, g ((sideE s).symm (Sum.inl i)) ((sideE s).symm (Sum.inr j)) := by
  have h1 : ∀ l, ∑ l', g l l' = ∑ j, g l ((sideE s).symm (Sum.inr j)) := by
    intro l
    rw [← Equiv.sum_comp (sideE s).symm (g l), Fintype.sum_sum_type]
    have h0 : ∑ i, g l ((sideE s).symm (Sum.inl i)) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_contra hne
      have h2 := (hg _ _ hne).2
      rw [side_inl s i] at h2
      simp at h2
    rw [h0, zero_add]
  rw [Finset.sum_congr rfl (fun l _ => h1 l),
    ← Equiv.sum_comp (sideE s).symm (fun l => ∑ j, g l ((sideE s).symm (Sum.inr j))),
    Fintype.sum_sum_type]
  have h3 : ∑ j, ∑ j', g ((sideE s).symm (Sum.inr j)) ((sideE s).symm (Sum.inr j')) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun j' _ => ?_))
    by_contra hne
    have h2 := (hg _ _ hne).1
    rw [side_inr s j] at h2
    simp at h2
  rw [h3, add_zero]
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
