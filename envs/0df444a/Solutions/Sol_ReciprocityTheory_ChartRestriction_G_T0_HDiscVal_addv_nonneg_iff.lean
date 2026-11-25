-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscVal.addv_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:40:57.750013+00:00
-- url     : https://prove2.me/submissions/c7dcffe3-8081-4670-9f6d-1114b2751d78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
open IsDedekindDomain WithZero ValPl
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
omit [IsFractionRing O F] [FiniteDimensional F L] [Algebra.IsSeparable F L] [IsScalarTower O F L]
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
theorem _root_.solution (v : HeightOneSpectrum (integralClosure O L)) {y : L} (hy : y ≠ 0) :
    0 ≤ addv L v y ↔ v.valuation L y ≤ 1 := by
  have hv : v.valuation L y ≠ 0 := by simpa using hy
  have hval : addv L v y = ((-WithZero.log (v.valuation L y) : ℤ) : WithTop ℤ) := by
    unfold addv
    rw [AddValuation.of_apply, if_neg hy]
  rw [hval]
  have h2 := WithZero.log_le_log hv one_ne_zero
  rw [WithZero.log_one] at h2
  constructor
  · intro h
    have h' : (0 : ℤ) ≤ -WithZero.log (v.valuation L y) := by exact_mod_cast h
    exact h2.1 (by omega)
  · intro h
    have h' := h2.2 h
    have h'' : (0 : ℤ) ≤ -WithZero.log (v.valuation L y) := by omega
    exact_mod_cast h''
end ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
