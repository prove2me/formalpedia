-- Prove2me | solution 1 for PretorsionImageClosed.isArtinianRing_moduleEnd_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:10:20.301966+00:00
-- url     : https://prove2.me/submissions/9734aedb-7a2a-433b-924c-b031e4250942

module
public import Mathlib.RingTheory.Artinian.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_ModuleTraces
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_EndomorphismRadical

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Function
open PretorsionImageClosed
universe u v
variable {A : Type u} {X : Type v}
variable [Ring A] [AddCommGroup X] [Module A X]
namespace PretorsionImageClosed
theorem _root_.solution
    {K B M : Type*}
    [Field K] [Ring B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module B M]
    [IsScalarTower K B M] [FiniteDimensional K M] :
    IsArtinianRing (Module.End B M) := by
  letI : Module.Finite K (Module.End B M) :=
    Module.Finite.of_injective
      (LinearMap.restrictScalarsₗ K B M M K)
      (LinearMap.restrictScalars_injective K)
  exact isArtinian_of_tower K inferInstance
end PretorsionImageClosed
