-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_length_int_quotient_map_5647412ff0d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:32:34.968612+00:00
-- url     : https://prove2.me/submissions/955ee535-1742-4ca7-848c-3254b4be055d

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
    Module.length ℤ (A' ⧸ I.map σ) = Module.length ℤ (A ⧸ I) :=
  ((Ideal.quotientEquiv I (I.map σ) σ rfl).toAddEquiv.toIntLinearEquiv.length_eq).symm
end GroundTheory.Heights₂.Heights
