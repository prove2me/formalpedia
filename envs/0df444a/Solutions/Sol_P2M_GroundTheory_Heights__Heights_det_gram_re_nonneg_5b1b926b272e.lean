-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_det_gram_re_nonneg_5b1b926b272e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:56.134981+00:00
-- url     : https://prove2.me/submissions/db7cc4aa-e80d-4572-926f-526ecfed5fae

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
    0 ≤ (det (gram ℂ w)).re :=
  (Complex.nonneg_iff.mp (det_gram_nonneg w)).1
end GroundTheory.Heights₂.Heights
