-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_eq_heisS_036f0895ef05
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:11.273428+00:00
-- url     : https://prove2.me/submissions/d98f4aa5-05ec-4291-913b-0e93d4419a11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix

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
variable {H : Matrix ι ι ℂ}
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {y : ι → ℂ} {s : ℂ} (hs : s + starRingEnd ℂ s + hForm H y y = 0) :
    s = heisS H y s.im := by
  apply Complex.ext
  · have := congrArg Complex.re hs
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    simp only [heisS]
    linarith
  · rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
