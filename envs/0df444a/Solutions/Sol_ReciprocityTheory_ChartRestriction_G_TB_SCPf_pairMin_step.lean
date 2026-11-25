-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.pairMin_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:31:21.88729+00:00
-- url     : https://prove2.me/submissions/477a814c-5263-4ce3-8b00-17ea864f31b4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
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
variable {π : Type} [Fintype π] [DecidableEq π]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (c : ι → π) (s : ι → Bool) (n : ι →₀ ℕ) (l l' : ι) (hc : c l = c l')
    (hs : s l = true) (hs' : s l' = false) :
    pairMin c s (n + Finsupp.single l 1 + Finsupp.single l' 1) = pairMin c s n + 1 := by
  have key : ∀ q : π,
      min (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = true),
          (n + Finsupp.single l 1 + Finsupp.single l' 1 : ι →₀ ℕ) x)
        (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = false),
          (n + Finsupp.single l 1 + Finsupp.single l' 1 : ι →₀ ℕ) x) =
      min (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = true), n x)
        (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = false), n x) +
        if c l = q then 1 else 0 := by
    intro q
    classical
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply, Finset.sum_ite_eq,
      Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hq : c l = q
    · have hq' : c l' = q := hc ▸ hq
      simp [hq, hq', hs, hs']
      try omega
    · have hq' : ¬ c l' = q := hc ▸ hq
      simp only [hq, hq', false_and, if_false]
      omega
  simp only [pairMin]
  rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
