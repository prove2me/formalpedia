-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_im_det_gram_c16ade0b03f4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:05.807871+00:00
-- url     : https://prove2.me/submissions/d385d6cb-a340-4945-897d-6dbf3e4385b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Extension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_nonneg_03110800f026

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
open Matrix
open scoped ComplexOrder
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → V) :
    (det (gram ℂ w)).im = 0 :=
  ((Complex.nonneg_iff.mp (det_gram_nonneg w)).2).symm
end GroundTheory.Heights₂.Heights
