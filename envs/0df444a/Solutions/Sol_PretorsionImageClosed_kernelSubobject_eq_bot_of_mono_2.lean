-- Prove2me | solution 2 for PretorsionImageClosed.kernelSubobject_eq_bot_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T04:24:11.31084+00:00
-- url     : https://prove2.me/submissions/f8218adc-fb80-4fa1-92f3-1e2cd40e1f57

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
variable {C : Type*} [Category C] [Abelian C]

/-- A monomorphism has zero kernel subobject. -/
theorem solution {X Y : C} (f : X ⟶ Y) [Mono f] : kernelSubobject f = ⊥ := by
  rw [kernelSubobject, Subobject.mk_eq_bot_iff_zero]
  exact (isZero_kernel_of_mono f).eq_zero_of_src (kernel.ι f)
