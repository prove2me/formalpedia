-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution.eq_monomial_of_dehomog_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:27:04.836016+00:00
-- url     : https://prove2.me/submissions/8a8fcbbc-902a-4dfa-8a4b-d701368dfc9f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PowFirstVarDvdSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_EvalOneBilinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_WH_wt_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_WH_wt_single


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
theorem _root_.solution (A : MvPolynomial (V D N) K) (m : ℕ) (hA : ∀ s ∈ A.support, WH.wt isX s = m)
    (k : K) (h1 : ev1 A = C k) : A = C k * X (Sum.inr 0) ^ m := by
  classical
  have hev1x0 : ev1 (X (Sum.inr 0) : MvPolynomial (V D N) K) = 1 := by simp [ev1]
  have hmono : ∀ (s : V D N →₀ ℕ) (a : K),
      ev1 (monomial s a) = monomial (s.erase (Sum.inr 0)) a := by
    intro s a
    have hs : monomial s a =
        monomial (s.erase (Sum.inr 0)) a * X (Sum.inr 0) ^ (s (Sum.inr 0)) := by
      rw [X_pow_eq_monomial, monomial_mul, mul_one, Finsupp.erase_add_single]
    rw [hs, map_mul, map_pow, hev1x0, one_pow, mul_one, ev1, aeval_monomial, monomial_eq,
      MvPolynomial.algebraMap_eq]
    congr 1
    apply Finsupp.prod_congr
    intro v hv
    rw [if_neg]
    rintro rfl
    simp at hv
  have hcoeff : ∀ u, coeff u (ev1 A) =
      ∑ s ∈ A.support, if s.erase (Sum.inr 0) = u then coeff s A else 0 := by
    intro u
    conv_lhs => rw [A.as_sum]
    rw [map_sum, coeff_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hmono, coeff_monomial]
  have hwt : ∀ s : V D N →₀ ℕ,
      WH.wt isX s = WH.wt isX (s.erase (Sum.inr 0)) + s (Sum.inr 0) := by
    intro s
    conv_lhs => rw [← Finsupp.erase_add_single (Sum.inr 0) s]
    rw [WH.wt_add, WH.wt_single, if_pos (show isX (Sum.inr 0 : V D N) from rfl)]
  have hwt0 : WH.wt isX (0 : V D N →₀ ℕ) = 0 := by simp [WH.wt]
  have hinj : ∀ s ∈ A.support, ∀ s' ∈ A.support,
      s.erase (Sum.inr 0) = s'.erase (Sum.inr 0) → s = s' := by
    intro s hs s' hs' he
    have h2 := hwt s
    have h3 := hwt s'
    rw [hA s hs] at h2
    rw [hA s' hs', ← he] at h3
    have h4 : s (Sum.inr 0) = s' (Sum.inr 0) := by omega
    rw [← Finsupp.erase_add_single (Sum.inr 0) s, ← Finsupp.erase_add_single (Sum.inr 0) s', he, h4]
  have hsingle : ∀ s ∈ A.support, s.erase (Sum.inr 0) = 0 → s = Finsupp.single (Sum.inr 0) m := by
    intro s hs hs0
    have h2 := hwt s
    rw [hA s hs, hs0, hwt0, zero_add] at h2
    rw [← Finsupp.erase_add_single (Sum.inr 0) s, hs0, zero_add, ← h2]
  ext u
  rw [coeff_C_mul, coeff_X_pow]
  by_cases hu : u ∈ A.support
  · have e := hcoeff (u.erase (Sum.inr 0))
    rw [Finset.sum_eq_single u (fun s hs hne => if_neg (fun h => hne (hinj s hs u hu h)))
      (fun h => absurd hu h), if_pos rfl, h1, coeff_C] at e
    rw [← e]
    by_cases h : Finsupp.single (Sum.inr 0) m = u
    · have h0 : 0 = u.erase (Sum.inr 0) := by
        rw [← h]
        simp
      rw [if_pos h0, if_pos h, mul_one]
    · have h0 : ¬ 0 = u.erase (Sum.inr 0) := fun h0 => h (hsingle u hu h0.symm).symm
      rw [if_neg h0, if_neg h, mul_zero]
  · have hu0 : coeff u A = 0 := by simpa using hu
    rw [hu0]
    by_cases h : Finsupp.single (Sum.inr 0) m = u
    · rw [if_pos h, mul_one]
      have e := hcoeff 0
      rw [h1, coeff_C, if_pos rfl] at e
      rw [e]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      rw [if_neg]
      intro hs0
      apply hu
      rw [← h, ← hsingle s hs hs0]
      exact hs
    · rw [if_neg h, mul_zero]
end ReciprocityTheory.ChartRestriction.G.T0.LinearSubstitution
