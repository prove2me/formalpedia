-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.SliceClasses.C_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:13.913827+00:00
-- url     : https://prove2.me/submissions/02ea7307-e6eb-448b-ae3c-1504de88fa31

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
theorem _root_.solution {P : Submodule ℂ U} {f : Module.End ℂ U} (hf : ∀ v ∈ P, f v ∈ P) :
    ∀ v ∈ P, (f - 1) v ∈ P := fun v hv => by
  rw [LinearMap.sub_apply, Module.End.one_apply]; exact P.sub_mem (hf v hv) hv
end PositivityTheory.Rg.Rs.SliceClasses
