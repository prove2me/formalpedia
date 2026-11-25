-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.SliceClasses.C_restrict_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:43.738028+00:00
-- url     : https://prove2.me/submissions/4a4a47ff-53eb-4360-8ba2-6f0d0e7dd680

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
    ∀ (m : ℕ) (x : P), (((f.restrict hf) ^ m) x : U) = (f ^ m) (x : U) := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ m ih => intro x; rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ',
      Module.End.mul_apply]
end PositivityTheory.Rg.Rs.SliceClasses
