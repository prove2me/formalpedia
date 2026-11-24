-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_map_ringEquiv_injective_a552ea8108be
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:51.560166+00:00
-- url     : https://prove2.me/submissions/13b7b1f8-1c7f-4a53-a38a-2ccfd2739603

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {A A' : Type*} [CommRing A] [CommRing A'] (σ : A ≃+* A')
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : Function.Injective (Ideal.map σ : Ideal A → Ideal A') :=
  fun I J hIJ => by
    rw [← Ideal.comap_map_of_bijective σ σ.bijective (I := I), hIJ,
      Ideal.comap_map_of_bijective σ σ.bijective]
end GroundTheory.Heights₂.Heights
