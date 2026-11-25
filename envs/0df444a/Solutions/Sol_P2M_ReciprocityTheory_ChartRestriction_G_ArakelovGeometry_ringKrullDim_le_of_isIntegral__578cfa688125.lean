-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_ringKrullDim_le_of_isIntegral__578cfa688125
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:51:52.7878+00:00
-- url     : https://prove2.me/submissions/a29823d9-3311-4f64-83f8-decb882f8dd5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  unfold ringKrullDim
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  intro P Q hPQ
  exact Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) hPQ
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
