-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.comp_mul_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:49.612973+00:00
-- url     : https://prove2.me/submissions/dee90b6e-69ad-4f2d-a62a-b73c4f37d7ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {σ : Type*} {M : Type*} [AddCancelCommMonoid M] [DecidableEq M] {w : σ → M}
    {ψ : MvPolynomial σ ℂ} {δ : M} (hψ : IsWeightedHomogeneous w ψ δ) (g : MvPolynomial σ ℂ) (n : M) :
    weightedHomogeneousComponent w (n + δ) (g * ψ) = weightedHomogeneousComponent w n g * ψ := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with hx
  · refine Finset.sum_congr rfl fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hb : coeff ab.2 ψ = 0
    · simp [hb]
    · have hwb := hψ hb
      have hsum : Finsupp.weight w ab.1 + Finsupp.weight w ab.2 = Finsupp.weight w x := by
        have hab' : ab.1 + ab.2 = x := by simpa using hab
        rw [← map_add, hab']
      have ha : Finsupp.weight w ab.1 = n := by
        rw [hwb, hx] at hsum
        exact add_right_cancel hsum
      rw [if_pos ha]
  · symm
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with ha
    · by_cases hb : coeff ab.2 ψ = 0
      · simp [hb]
      · exfalso
        apply hx
        have hwb := hψ hb
        have hab' : ab.1 + ab.2 = x := by simpa using hab
        rw [← hab', map_add, ha, hwb]
    · simp
end ReciprocityTheory.ChartRestriction.G.Geo
