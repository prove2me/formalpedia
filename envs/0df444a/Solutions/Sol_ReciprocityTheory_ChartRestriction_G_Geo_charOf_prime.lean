-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.charOf_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:44.375288+00:00
-- url     : https://prove2.me/submissions/e7b86bca-82f0-4e93-a7b7-cfdae7cdcbb9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp

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
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {W : Ideal (MRing ι)} (hW : W.IsPrime) (hv : ¬ IsHorizontal W) :
    (charOf W).Prime := by
  have := hW
  have hJ : (W.comap (C : ℤ →+* MRing ι)).IsPrime := inferInstance
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ≠ 0 := fun h0 =>
    hv ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mpr h0)
  unfold charOf
  rw [← Int.prime_iff_natAbs_prime, ← Ideal.span_singleton_prime hg,
    Ideal.span_singleton_generator]
  exact hJ
end ReciprocityTheory.ChartRestriction.G.Geo
