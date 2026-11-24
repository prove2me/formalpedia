-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.eq_C_of_pderiv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:51:00.253474+00:00
-- url     : https://prove2.me/submissions/81847e4a-ab89-44d4-95c3-cfde14c909b2

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgebraicIndependentOfDerivations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
theorem _root_.solution {K ι : Type*} [Field K] [CharZero K] (P : MvPolynomial ι K)
    (h : ∀ i, pderiv i P = 0) : P.totalDegree = 0 := by
  classical
  by_contra hne
  obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support
    (Finset.nonempty_of_ne_empty (by rintro hs; apply hne; simp [totalDegree, hs]))
    (fun s => s.sum fun _ e => e)
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    simpa [totalDegree] using hmd
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm0 (Finsupp.ext hc)
  have hc := congrArg (coeff (m - Finsupp.single i 1)) (h i)
  rw [coeff_pderiv, coeff_zero] at hc
  have hm' : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
    ext k
    by_cases hk : k = i
    · subst hk; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hk]
  rw [hm'] at hc
  rcases mul_eq_zero.mp hc with h1 | h1
  · exact (mem_support_iff.mp hm) h1
  · exact Nat.cast_add_one_ne_zero _ h1
end ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
