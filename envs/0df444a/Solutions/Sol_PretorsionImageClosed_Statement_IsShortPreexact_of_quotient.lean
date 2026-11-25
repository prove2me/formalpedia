-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsShortPreexact.of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:37.794535+00:00
-- url     : https://prove2.me/submissions/3ead46bc-b733-4b5e-b414-6505126f8c24

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lifting
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_comp_left


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] {Z : ObjectProperty C}
namespace PretorsionImageClosed.Statement
namespace IsShortPreexact
theorem _root_.solution {X V A B F : C} (π : X ⟶ V) [Epi π] (ι : A ⟶ X) [Mono ι]
    (πA : A ⟶ B) [Epi πA] (uV : B ⟶ V) [Mono uV] (vV : V ⟶ F) (hs : IsShortPreexact Z uV vV)
    (hcomm : πA ≫ uV = ι ≫ π)
    (hpull : ∀ {Y : C} (u' : Y ⟶ X) (w : Y ⟶ B), w ≫ uV = u' ≫ π → ∃ w' : Y ⟶ A, w' ≫ ι = u')
    (hK : ∀ {W : C} (g : A ⟶ W), Z W → kernel.ι πA ≫ g = 0) :
    IsShortPreexact Z ι (π ≫ vV) := by
  have htriv : IsTrivial Z (ι ≫ π ≫ vV) := by
    rw [← Category.assoc, ← hcomm, Category.assoc]
    exact hs.1.1.comp_left πA
  refine ⟨⟨htriv, fun {Y} u' hu' => ?_⟩, ⟨htriv, fun {Y} v' hv' => ?_⟩⟩
  · -- the prekernel property
    rw [← Category.assoc] at hu'
    obtain ⟨w, hw, -⟩ := hs.1.2 _ hu'
    obtain ⟨w', hw'⟩ := hpull u' w hw
    exact ⟨w', hw', fun w'' hw'' => (cancel_mono ι).1 (hw''.trans hw'.symm)⟩
  · -- the precokernel property
    obtain ⟨W, hW, g, h, hgh⟩ := hv'
    -- `v'` vanishes on the kernel of `π`
    obtain ⟨k, hk⟩ := hpull (kernel.ι π) 0 (by rw [zero_comp, kernel.condition])
    have hkπ : k ≫ πA = 0 := by
      rw [← cancel_mono uV, Category.assoc, hcomm, ← Category.assoc, hk, kernel.condition, zero_comp]
    have hker : kernel.ι π ≫ v' = 0 := by
      rw [← hk, Category.assoc, ← hgh, ← kernel.lift_ι πA k hkπ, Category.assoc, ← Category.assoc
        (kernel.ι πA), hK g hW, zero_comp, comp_zero]
    set d := Abelian.epiDesc π v' hker with hd
    have hπd : π ≫ d = v' := Abelian.comp_epiDesc π v' hker
    -- `u_V ≫ d` is trivial
    have hd' : IsTrivial Z (uV ≫ d) := by
      refine ⟨W, hW, Abelian.epiDesc πA g (hK g hW), h, ?_⟩
      rw [← cancel_epi πA, ← Category.assoc, Abelian.comp_epiDesc, hgh, ← Category.assoc, hcomm,
        Category.assoc, hπd]
    obtain ⟨e, he, huniq⟩ := hs.2.2 d hd'
    have he0 : vV ≫ e = d := he
    refine ⟨e, ?_, fun e' he' => huniq e' ?_⟩
    · show (π ≫ vV) ≫ e = v'
      rw [Category.assoc, he0, hπd]
    · have he1 : (π ≫ vV) ≫ e' = v' := he'
      show vV ≫ e' = d
      rw [← cancel_epi π, ← Category.assoc, he1, hπd]
end IsShortPreexact
end PretorsionImageClosed.Statement
