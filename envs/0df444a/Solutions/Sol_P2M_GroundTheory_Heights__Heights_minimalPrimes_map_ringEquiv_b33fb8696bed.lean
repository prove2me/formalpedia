-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_minimalPrimes_map_ringEquiv_b33fb8696bed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:41.203192+00:00
-- url     : https://prove2.me/submissions/c1a9f922-2ec8-4cdd-a844-8c1a5117e8e5

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
theorem _root_.solution (I : Ideal A) :
    (I.map σ).minimalPrimes = Ideal.map σ '' I.minimalPrimes := by
  have := Ideal.minimalPrimes_map_of_surjective (f := (σ : A →+* A')) σ.surjective I
  rw [RingHom.ker_coe_equiv, sup_bot_eq] at this
  exact this
end GroundTheory.Heights₂.Heights
