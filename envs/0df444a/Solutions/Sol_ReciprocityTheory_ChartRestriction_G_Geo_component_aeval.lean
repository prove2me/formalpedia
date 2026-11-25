-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.component_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:54.448496+00:00
-- url     : https://prove2.me/submissions/b0a3bd23-750c-43ff-9555-424d9a087a5d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
private theorem aeval_of_isWeightedHomogeneous_blkWt {E : Type*} (w' : E → (K →₀ ℕ))
    (yt : E → MvPolynomial (Σ k, ι k) ℚ)
    (hy : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (w' e)) (n : E →₀ ℕ) (c : ℚ) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (aeval yt (monomial n c)) (Finsupp.weight w' n) := by
  classical
  rw [aeval_monomial, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
  have h0 : IsWeightedHomogeneous (blkWt (ι := ι))
      (algebraMap ℚ (MvPolynomial (Σ k, ι k) ℚ) c) 0 := by
    rw [MvPolynomial.algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  have h1 := h0.mul (IsWeightedHomogeneous.prod n.support (fun e => yt e ^ n e)
    (fun e => n e • w' e) (fun e _ => (hy e).pow (n e)))
  simpa using h1
variable (k0 : K)
end
end ReciprocityTheory.ChartRestriction.G.Geo
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {E : Type*} (w' : E → (K →₀ ℕ))
    (yt : E → MvPolynomial (Σ k, ι k) ℚ)
    (hy : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (w' e)) (H : MvPolynomial E ℚ)
    (δ : K →₀ ℕ) :
    weightedHomogeneousComponent (blkWt (ι := ι)) δ (aeval yt H) =
      aeval yt (weightedHomogeneousComponent w' δ H) := by
  induction H using MvPolynomial.induction_on' with
  | monomial n c =>
    by_cases h : Finsupp.weight w' n = δ
    · subst h
      rw [(aeval_of_isWeightedHomogeneous_blkWt w' yt hy n c).weightedHomogeneousComponent_same,
        (isWeightedHomogeneous_monomial w' n c rfl).weightedHomogeneousComponent_same]
    · rw [(aeval_of_isWeightedHomogeneous_blkWt w' yt hy n c).weightedHomogeneousComponent_ne δ (Ne.symm h),
        (isWeightedHomogeneous_monomial w' n c rfl).weightedHomogeneousComponent_ne δ (Ne.symm h),
        map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
end ReciprocityTheory.ChartRestriction.G.Geo
