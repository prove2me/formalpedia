-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_prod_X_pow_44da1a552808
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:31.226326+00:00
-- url     : https://prove2.me/submissions/2347d30a-d54f-4b37-a6e2-55a2dccd3d6f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_prod_X_pow_eq_monomial_fintype_a59d57b5530c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {O : Type*} [CommRing O] [IsDomain O]
omit [IsDomain O]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (m : Ideal O) [hm : m.IsPrime] (a : ι → ℕ) :
    IsUnit (algebraMap (MvPolynomial ι O) (locB ι m) (∏ k, X k ^ a k)) := by
  have hnot : (∏ k, X k ^ a k : MvPolynomial ι O) ∉ fibO ι m := by
    intro h
    have h' := MvPolynomial.mem_map_C_iff.mp h (Finsupp.equivFunOnFinite.symm a)
    rw [prod_X_pow_eq_monomial_fintype, coeff_monomial, if_pos rfl] at h'
    exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr h')
  exact IsLocalization.map_units (locB ι m) (⟨∏ k, X k ^ a k, hnot⟩ : (fibO ι m).primeCompl)
end GroundTheory.Heights₂.Heights.OrbitChartMult
