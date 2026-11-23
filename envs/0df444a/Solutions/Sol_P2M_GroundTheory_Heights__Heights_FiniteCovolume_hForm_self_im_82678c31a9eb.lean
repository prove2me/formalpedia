-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_self_im_82678c31a9eb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:11.510604+00:00
-- url     : https://prove2.me/submissions/3144ea8e-d0ee-414e-9312-c322b4dff6b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_hForm_conj_a26db4eadf30

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable (H : Matrix ι ι ℂ)
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (u : ι → ℂ) :
    (hForm H u u).im = 0 :=
  Complex.conj_eq_iff_im.1 (hForm_conj hH u u)
end GroundTheory.Heights₂.Heights.FiniteCovolume
