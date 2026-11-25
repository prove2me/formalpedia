-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_locB_injective_c62a6c2c8081
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:16.697856+00:00
-- url     : https://prove2.me/submissions/2ad33e8c-c55b-46b3-8fdb-936aa0d016ab

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
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (ι : Type) (m : Ideal O) [m.IsPrime] :
    Function.Injective (algebraMap (MvPolynomial ι O) (locB ι m)) :=
  IsLocalization.injective (locB ι m) (Ideal.primeCompl_le_nonZeroDivisors (fibO ι m))
end GroundTheory.Heights₂.Heights.OrbitChartMult
