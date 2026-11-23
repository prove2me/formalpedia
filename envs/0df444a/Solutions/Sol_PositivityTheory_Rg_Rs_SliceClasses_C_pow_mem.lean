-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.SliceClasses.C_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:31.209857+00:00
-- url     : https://prove2.me/submissions/1f164072-e371-4094-bd05-6e4db40ad4a9

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
    ∀ k : ℕ, ∀ v ∈ P, (f ^ k) v ∈ P := by
  intro k
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih => intro v hv; rw [pow_succ', Module.End.mul_apply]; exact hf _ (ih v hv)
end PositivityTheory.Rg.Rs.SliceClasses
