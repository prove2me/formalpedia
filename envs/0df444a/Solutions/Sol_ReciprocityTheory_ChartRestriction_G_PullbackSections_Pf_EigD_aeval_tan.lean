-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.aeval_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:13.232579+00:00
-- url     : https://prove2.me/submissions/53ee31ed-72cc-48b3-9565-0c69644101e8

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SingleMemDegLE

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
theorem _root_.solution {ι : Type} [DecidableEq ι] (ℓ : ι) (P : MvPolynomial ι V) :
    aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber V) else 0) P =
      algebraMap V (DualNumber V) (constantCoeff P) + coeff (Finsupp.single ℓ 1) P • DualNumber.eps := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.aeval_C, MvPolynomial.constantCoeff_C, MvPolynomial.coeff_C,
      if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, zero_smul, add_zero]
  | add p q hp hq => rw [map_add, hp, hq, map_add, map_add, MvPolynomial.coeff_add, add_smul]; abel
  | mul_X p n hp =>
    rw [map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, zero_add,
      MvPolynomial.coeff_mul_X']
    by_cases h : n = ℓ
    · subst h
      have hs : n ∈ (Finsupp.single n (1 : ℕ)).support := by simp
      rw [if_pos rfl, if_pos hs, tsub_self, ← MvPolynomial.constantCoeff_eq, add_mul, smul_mul_assoc,
        DualNumber.eps_mul_eps, smul_zero, add_zero, Algebra.smul_def]
    · have : n ∉ (Finsupp.single ℓ 1).support := by simp [Finsupp.support_single_ne_zero, Ne.symm h, h]
      simp [h, this]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
