-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.SliceClasses.C_comm_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:13.821662+00:00
-- url     : https://prove2.me/submissions/07d622b2-a52a-492c-a460-868fb3664d7a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_PSliceC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.SliceClasses
variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] {ι : Type*}
namespace PositivityTheory.Rg.Rs.SliceClasses
theorem _root_.solution {M : ι → Module.End ℂ U} (hc : ∀ i j, Commute (M i) (M j)) (i j : ι) (k : ℕ) (x : U) :
    M j (((M i - 1) ^ k) x) = ((M i - 1) ^ k) (M j x) := by
  have h : Commute (M j) ((M i - 1) ^ k) := ((hc j i).sub_right (Commute.one_right _)).pow_right k
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply]
end PositivityTheory.Rg.Rs.SliceClasses
