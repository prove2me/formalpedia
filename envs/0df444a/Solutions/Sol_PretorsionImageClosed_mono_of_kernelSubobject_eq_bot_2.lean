-- Prove2me | solution 2 for PretorsionImageClosed.mono_of_kernelSubobject_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T04:24:13.534078+00:00
-- url     : https://prove2.me/submissions/38438d51-850b-4935-84e4-499b85ff9a3e

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

/-- A morphism with zero kernel subobject is a monomorphism. -/
theorem solution {X Y : C} (f : X ⟶ Y) (h : kernelSubobject f = ⊥) : Mono f := by
  rw [kernelSubobject, Subobject.mk_eq_bot_iff_zero] at h
  exact Preadditive.mono_of_kernel_zero h
