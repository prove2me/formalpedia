-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.isImageClosed_of_intersectionClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:50:08.600649+00:00
-- url     : https://prove2.me/submissions/afee8e74-885d-4fe7-80df-dd59d001d775

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_SummandReduction
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_interval_of_epi
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_exists_interval_of_mono
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSum
public import Theorems.Thm_PretorsionImageClosed_Statement_isImageClosed_iff_forall_imageSubobject


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (C : Subcategory (Statement.LinRep k n))
    (hC : IntersectionClosed C) : C.IsImageClosed := by
  rw [Statement.isImageClosed_iff_forall_imageSubobject]
  intro X Y f hX hY
  -- a summand `Z` of the image which is a quotient of `X` and a subobject of `Y` lies in `C`
  suffices h : ∀ Z : Statement.LinRep k n, IntervalSum Z →
      (∃ p : X ⟶ Z, Epi p) → (∃ i : Z ⟶ Y, Mono i) → C.prop Z from
    h _ (intervalSum _) ⟨factorThruImageSubobject f, inferInstance⟩
      ⟨(imageSubobject f).arrow, inferInstance⟩
  intro Z hZ
  induction hZ with
  | zero hz =>
    intro _ _
    exact C.prop_of_isZero hz
  | @step Z Z' a b hab h' e ih =>
    rintro ⟨p, hp⟩ ⟨i, hi⟩
    refine C.prop_of_iso e.symm (C.prop_biprod ?_ (ih ⟨p ≫ e.hom ≫ biprod.snd, epi_comp _ _⟩
      ⟨biprod.inr ≫ e.inv ≫ i, mono_comp _ _⟩))
    -- the interval summand `M_{a,b}`
    obtain ⟨d, hbd, hd⟩ := exists_interval_of_epi C hab hX (p ≫ e.hom ≫ biprod.fst)
    obtain ⟨c, hca, hc⟩ := exists_interval_of_mono C hab hY (biprod.inl ≫ e.inv ≫ i)
    have := hC a d c b (hab.trans hbd) (hca.trans hab) hd hc (by
      rw [max_eq_left hca, min_eq_right hbd]; exact hab)
    rwa [max_eq_left hca, min_eq_right hbd] at this
end PretorsionImageClosed.LinearQuiver
