-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.isFractionRing_Op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:37:50.610972+00:00
-- url     : https://prove2.me/submissions/b9f6d165-b804-4daf-b306-1ec106059ad7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_isFractionRing_OT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (la : HeightOneSpectrum (𝓞 K)) :
    letI := algOpKT (K := K) D N la
    IsFractionRing (Op D N la) (KTf K D N) := by
  letI := algOTKT (K := K) D N
  letI := algOpKT (K := K) D N la
  haveI := isFractionRing_OT (K := K) D N
  haveI : IsScalarTower (OT K D N) (Op D N la) (KTf K D N) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = OpToKT D N la (algebraMap _ _ x)
      rw [OpToKT, IsLocalization.lift_eq]
      rfl
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (laT D N la).primeCompl
    (Op D N la) (KTf K D N)
end ReciprocityTheory.ChartRestriction.G.T0
