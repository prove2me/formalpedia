-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.clear_denoms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:58.354982+00:00
-- url     : https://prove2.me/submissions/958b6eb5-6430-4903-8ca6-60800125f9b3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisExtend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteDimensionalOfLiftY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
open MvPolynomial
variable {A : Type} [CommRing A] [IsDomain A] {σ : Type}
namespace ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
theorem _root_.solution (P : MvPolynomial σ (FractionRing A)) :
    ∃ (b : A) (p : MvPolynomial σ A), b ≠ 0 ∧
      MvPolynomial.map (algebraMap A (FractionRing A)) p =
        MvPolynomial.C (algebraMap A (FractionRing A) b) * P := by
  induction P using MvPolynomial.induction_on
  next a =>
    obtain ⟨z, hz⟩ := IsLocalization.surj (nonZeroDivisors A) a
    refine ⟨z.2, C z.1, nonZeroDivisors.coe_ne_zero z.2, ?_⟩
    rw [MvPolynomial.map_C, ← hz, MvPolynomial.C_mul, mul_comm]
  next p q hp hq =>
    obtain ⟨b₁, p₁, hb₁, h₁⟩ := hp
    obtain ⟨b₂, p₂, hb₂, h₂⟩ := hq
    refine ⟨b₁ * b₂, C b₂ * p₁ + C b₁ * p₂, mul_ne_zero hb₁ hb₂, ?_⟩
    simp only [_root_.map_add, _root_.map_mul, MvPolynomial.map_C, h₁, h₂]
    ring
  next p n hp =>
    obtain ⟨b, q, hb, h⟩ := hp
    exact ⟨b, q * X n, hb, by rw [_root_.map_mul, MvPolynomial.map_X, h, mul_assoc]⟩
end ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
