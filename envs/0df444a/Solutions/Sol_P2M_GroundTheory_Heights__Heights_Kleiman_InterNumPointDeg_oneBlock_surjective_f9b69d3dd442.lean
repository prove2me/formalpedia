-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_InterNumPointDeg_oneBlock_surjective_f9b69d3dd442
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:12:39.583807+00:00
-- url     : https://prove2.me/submissions/e09730f4-6741-4255-ac59-98cdc95b5a85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PInterNumPointDeg

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
theorem _root_.solution (f : Poly k N) :
    oneBlock (S := k) (N := N) (rename (HilbertPositive.blockEquiv N).symm f) = f := by
  rw [oneBlock, rename_rename]
  exact (congrArg (fun g => rename g f) (HilbertPositive.blockEquiv N).self_comp_symm).trans (rename_id_apply f)
end GroundTheory.Heights₂.Heights.Kleiman.InterNumPointDeg
