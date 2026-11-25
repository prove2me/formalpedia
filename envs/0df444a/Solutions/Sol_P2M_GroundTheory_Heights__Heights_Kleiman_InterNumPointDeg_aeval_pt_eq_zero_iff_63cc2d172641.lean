-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_eq_zero_iff_63cc2d172641
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:28:23.643735+00:00
-- url     : https://prove2.me/submissions/ded5c955-3175-4c73-8de0-a63c10d78a02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumPointDeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_coneHom_eq_zero_iff_9bc14c5accda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_aeval_pt_oneBlock_f43e82ddc549
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_oneBlock_surjective_f9b69d3dd442

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
variable {k : Type u} [Field k] {N : ℕ}
variable [Small.{w} k] (pp : Ideal (Poly k N)) [pp.IsPrime]
namespace GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
theorem _root_.solution (f : Poly k N) : aeval (pt.{u, w} pp) f = 0 ↔ f ∈ pp := by
  rw [← oneBlock_surjective f, aeval_pt_oneBlock, coneHom_eq_zero_iff]
end GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
