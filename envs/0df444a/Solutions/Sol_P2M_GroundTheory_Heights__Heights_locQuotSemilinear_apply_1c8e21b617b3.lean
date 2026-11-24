-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_locQuotSemilinear_apply_1c8e21b617b3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:38.933811+00:00
-- url     : https://prove2.me/submissions/fc2b67af-4283-4784-b82d-c487d45bf40d

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
variable (J V : Ideal A) [V.IsPrime] [(V.map σ).IsPrime]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : LocalizedModule V.primeCompl (A ⧸ J)) :
    locQuotSemilinear σ J V x = locQuotMap σ J V x := rfl
end GroundTheory.Heights₂.Heights
