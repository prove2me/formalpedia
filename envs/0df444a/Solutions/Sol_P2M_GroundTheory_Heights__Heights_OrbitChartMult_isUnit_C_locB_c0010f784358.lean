-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_isUnit_C_locB_c0010f784358
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:58:58.965135+00:00
-- url     : https://prove2.me/submissions/c5375439-9539-476e-87d7-04b6d11ccd9d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMult

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
omit [Fintype ι] [DecidableEq ι] [IsDomain O]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (m : Ideal O) [m.IsPrime] (u : m.primeCompl) :
    IsUnit (((algebraMap (MvPolynomial ι O) (locB ι m)).comp C) (u : O)) := by
  classical
  have hnot : (C (u : O) : MvPolynomial ι O) ∉ fibO ι m := fun h ↦ u.2 (by
    have h' := MvPolynomial.mem_map_C_iff.mp h 0
    rwa [coeff_C, if_pos rfl] at h')
  exact IsLocalization.map_units (locB ι m) (⟨C (u : O), hnot⟩ : (fibO ι m).primeCompl)
end GroundTheory.Heights₂.Heights.OrbitChartMult
