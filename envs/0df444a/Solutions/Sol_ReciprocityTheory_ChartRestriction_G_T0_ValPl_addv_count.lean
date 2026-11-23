-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.addv_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:00:51.239751+00:00
-- url     : https://prove2.me/submissions/8bd0ec3e-926a-493e-ae2a-136189f0adf1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain WithZero IsLocalRing
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution (v : HeightOneSpectrum (integralClosure O L)) (b : integralClosure O L)
    (hb : b ≠ 0) :
    addv L v (algebraMap (integralClosure O L) L b) =
      ((Multiset.count v.asIdeal
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) : ℕ) : WithTop ℤ) := by
  have hx : algebraMap (integralClosure O L) L b ≠ 0 := by
    intro h
    apply hb
    apply IsFractionRing.injective (integralClosure O L) L
    rw [h, map_zero]
  have hI : Ideal.span {b} ≠ 0 := by
    first
    | (rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb)
    | simpa using hb
  have hc := Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot
  have hval : v.valuation L (algebraMap (integralClosure O L) L b) = v.intValuation b := by
    first
    | exact v.valuation_of_algebraMap b
    | exact HeightOneSpectrum.valuation_of_algebraMap v b
    | simp
  rw [addv_apply v hx, hval, v.intValuation_if_neg hb, log_exp, neg_neg, hc]
  first
  | (norm_cast; done)
  | (norm_cast; convert rfl; done)
  | (push_cast; convert rfl; done)
  | (congr 1; convert rfl)
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
