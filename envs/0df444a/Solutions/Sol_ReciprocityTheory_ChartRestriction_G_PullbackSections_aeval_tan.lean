-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.aeval_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:59:01.657365+00:00
-- url     : https://prove2.me/submissions/7150f27d-18b1-4a78-824d-6038bf09d8ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {Y : Scheme.{0}}
variable {K : Type} [Field K] {ι : Type} [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (ℓ : ι) (q : MvPolynomial ι K) :
    MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber K) else 0) q =
      TrivSqZeroExt.inl (MvPolynomial.constantCoeff q) +
        TrivSqZeroExt.inr (MvPolynomial.coeff (Finsupp.single ℓ 1) q) := by
  induction q using MvPolynomial.induction_on
  next a =>
    have hs : (0 : ι →₀ ℕ) ≠ Finsupp.single ℓ 1 := (Finsupp.single_ne_zero.2 one_ne_zero).symm
    ext <;> simp [MvPolynomial.coeff_C, hs, TrivSqZeroExt.algebraMap_eq_inl]
  next p q hp hq =>
    simp only [map_add, hp, hq, MvPolynomial.coeff_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel
  next p i hp =>
    rw [map_mul, hp, MvPolynomial.aeval_X]
    by_cases h : i = ℓ
    · subst h
      have hc : MvPolynomial.coeff (Finsupp.single i 1) (p * MvPolynomial.X i) =
          MvPolynomial.constantCoeff p := by
        have := MvPolynomial.coeff_mul_X (0 : ι →₀ ℕ) i p
        rw [zero_add] at this
        exact this
      rw [hc]
      ext <;> simp
    · have h' : ℓ ≠ i := Ne.symm h
      have hc : MvPolynomial.coeff (Finsupp.single ℓ 1) (p * MvPolynomial.X i) = 0 := by
        rw [MvPolynomial.coeff_mul_X']
        simp [Finsupp.single_apply, h', h]
      rw [hc]
      ext <;> simp [h]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
