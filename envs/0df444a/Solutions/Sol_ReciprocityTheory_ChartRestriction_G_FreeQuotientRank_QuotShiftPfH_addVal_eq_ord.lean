-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH.addVal_eq_ord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:59.955418+00:00
-- url     : https://prove2.me/submissions/9aa864fb-ee59-456a-855b-2ac59b58bb85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotShiftPfH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
open IsDedekindDomain
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] (v : HeightOneSpectrum R)
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
theorem _root_.solution (x : Rv F v) (hx : (x : F) ≠ 0) :
    IsDiscreteValuationRing.addVal (Rv F v) x = ((ordAt v (x : F)).toNat : ℕ∞) := by
  obtain ⟨π, h0, h1⟩ := exists_ord_one (F := F) v
  obtain ⟨u, hu⟩ := eq_unit_mul_pow v h0 h1 x hx
  conv_lhs => rw [hu]
  exact IsDiscreteValuationRing.addVal_def' u (irreducible_of_ord_one v h0 h1) _
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotShiftPfH
