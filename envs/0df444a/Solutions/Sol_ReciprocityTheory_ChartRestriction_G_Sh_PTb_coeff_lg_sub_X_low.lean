-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.coeff_lg_sub_X_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:28:37.040796+00:00
-- url     : https://prove2.me/submissions/ece29071-6c5a-42e1-b400-adca0f3ff28a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_card_toMultiset_eq_degree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C]
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) (a : Fin d) (e : Fin d →₀ ℕ) (he : e.degree ≤ 1) :
    coeff e (G.lg a - X a) = 0 := by
  rw [map_sub, coeff_X]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with h0 | h1
  · have e0 : e = 0 := by
      first
      | exact (Finsupp.degree_eq_zero_iff e).mp h0
      | exact Finsupp.degree_eq_zero_iff.mp h0
    subst e0
    have hs : (0 : Fin d →₀ ℕ) ≠ Finsupp.single a 1 := by
      intro h
      have := congrArg (fun f : Fin d →₀ ℕ => f a) h
      simp at this
    rw [if_neg hs, coeff_zero_eq_constantCoeff_apply, G.lg_const a, sub_zero]
  · obtain ⟨b, hb⟩ : ∃ b, e.toMultiset = {b} := by
      apply Multiset.card_eq_one.mp
      rw [card_toMultiset_eq_degree, h1]
    have eb : e = Finsupp.single b 1 := by
      have h2 : Multiset.toFinsupp (Finsupp.toMultiset e) = e := Finsupp.toMultiset_toFinsupp e
      rw [← h2, hb]
      first
      | exact Multiset.toFinsupp_singleton b
      | simp
    subst eb
    rw [G.lg_lin a b]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : Finsupp.single b 1 ≠ Finsupp.single a 1 := by
        intro h
        exact hab ((Finsupp.single_left_inj one_ne_zero).mp h).symm
      rw [if_neg hab, if_neg hne, sub_zero]
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
