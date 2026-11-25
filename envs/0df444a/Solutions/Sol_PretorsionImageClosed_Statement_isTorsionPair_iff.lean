-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isTorsionPair_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:52:37.485899+00:00
-- url     : https://prove2.me/submissions/e7fbbd68-c08c-4f66-94d1-ac67c10bbc6b

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_FixedMiddle
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Definitions.Def_PretorsionImageClosed_Pretorsion_TorsionPairs
public import Theorems.Thm_PretorsionImageClosed_Statement_isTrivial_iff_eq_zero
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrecokernel_epi
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPrekernel_mono
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_mono


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory ZeroObject
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed.Statement
theorem _root_.solution (T F : Subcategory C) :
    IsTorsionPair T.prop F.prop ↔
      IsPretorsionTheory T.prop F.prop ∧ ∀ X, (T.prop ⊓ F.prop) X → IsZero X := by
  constructor
  · rintro ⟨h0, hseq⟩
    have hZ : ∀ X, (T ⊓ F).prop X → IsZero X := fun X hX => by
      rw [IsZero.iff_id_eq_zero]
      exact h0 (𝟙 X) hX.1 hX.2
    have htriv : ∀ {X Y : C} (f : X ⟶ Y), IsTrivial (T.prop ⊓ F.prop) f ↔ f = 0 :=
      fun f => isTrivial_iff_eq_zero (Z := T ⊓ F) hZ f
    refine ⟨⟨fun f hX hY => (htriv f).2 (h0 f hX hY), fun X => ?_⟩, hZ⟩
    obtain ⟨T', F', u, v, w, hT', hF', hSE⟩ := hseq X
    haveI := hSE.mono_f
    haveI := hSE.epi_g
    have hK := hSE.exact.fIsKernel
    have hC := hSE.exact.gIsCokernel
    refine ⟨T', F', u, v, hT', hF', ⟨⟨(htriv _).2 w, fun {Y} u' hu' => ?_⟩,
      ⟨(htriv _).2 w, fun {Y} v' hv' => ?_⟩⟩⟩
    · obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hK u' ((htriv _).1 hu')
      exact ⟨l, hl, fun l' hl' => (cancel_mono u).1 (hl'.trans hl.symm)⟩
    · obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hC v' ((htriv _).1 hv')
      exact ⟨l, hl, fun l' hl' => (cancel_epi v).1 (hl'.trans hl.symm)⟩
  · rintro ⟨hP, hZ⟩
    have htriv : ∀ {X Y : C} (f : X ⟶ Y), IsTrivial (T.prop ⊓ F.prop) f ↔ f = 0 :=
      fun f => isTrivial_iff_eq_zero (Z := T ⊓ F) hZ f
    refine ⟨fun f hX hY => (htriv f).1 (hP.1 f hX hY), fun X => ?_⟩
    obtain ⟨T', F', u, v, hT', hF', hu, hv⟩ := hP.2 X
    have w : u ≫ v = 0 := (htriv _).1 hu.1
    haveI := hu.mono
    haveI := hv.epi
    refine ⟨T', F', u, v, w, hT', hF', ⟨?_⟩⟩
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι _ _ (fun g hg => (hu.2 g ((htriv _).2 hg)).exists.choose)
      (fun g hg => (hu.2 g ((htriv _).2 hg)).exists.choose_spec) (fun g hg m hm => ?_)
    exact (hu.2 g ((htriv _).2 hg)).unique hm (hu.2 g ((htriv _).2 hg)).exists.choose_spec
end PretorsionImageClosed.Statement
