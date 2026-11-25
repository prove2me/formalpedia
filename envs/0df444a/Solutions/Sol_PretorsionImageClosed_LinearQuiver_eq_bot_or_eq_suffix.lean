-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.eq_bot_or_eq_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:21:02.760966+00:00
-- url     : https://prove2.me/submissions/edf93a8b-630d-4519-9aea-21e43f59b4fc

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_mono_biprod_desc
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_mk_eq_suffix_of_mono
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_and_le_of_mono
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_intervalSum


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
theorem _root_.solution {a d : Fin n} (K : Subobject (interval k a d)) :
    K = ⊥ ∨ ∃ (ℓ : Fin n) (hal : a ≤ ℓ), ℓ ≤ d ∧ K = suffix a d ℓ hal := by
  rcases intervalSum (K : Statement.LinRep k n) with hz | @⟨_, K', c, e, hce, h', e'⟩
  · left
    rw [← Subobject.mk_arrow K, Subobject.mk_eq_bot_iff_zero]
    exact hz.eq_zero_of_src _
  · right
    -- the first summand embeds into `M_{a,d}`
    set ι : interval k c e ⟶ interval k a d := biprod.inl ≫ e'.inv ≫ K.arrow with hι
    haveI : Mono ι := mono_comp _ _
    obtain ⟨rfl, hac⟩ := eq_and_le_of_mono hce ι
    -- the other summand is zero
    have hK'z : IsZero K' := by
      by_contra hK'nz
      rcases h' with hz' | @⟨_, K'', c', d', hcd', -, e''⟩
      · exact hK'nz hz'
      · set ι' : interval k c' d' ⟶ interval k a e :=
          biprod.inl ≫ e''.inv ≫ biprod.inr ≫ e'.inv ≫ K.arrow with hι'
        haveI : Mono ι' := mono_comp _ _
        obtain ⟨rfl, hac'⟩ := eq_and_le_of_mono hcd' ι'
        -- the two intervals together embed, contradiction
        have hdesc : biprod.desc ι ι' =
            (biprod.map (𝟙 _) (biprod.inl ≫ e''.inv)) ≫ e'.inv ≫ K.arrow := by
          apply biprod.hom_ext' <;> simp [hι, hι']
        have hm : Mono (biprod.desc ι ι') := by
          rw [hdesc]
          haveI : Mono (biprod.inl ≫ e''.inv : interval k c' d' ⟶ K') := mono_comp _ _
          haveI : Mono (biprod.map (𝟙 (interval k c d')) (biprod.inl ≫ e''.inv) :
              interval k c d' ⊞ interval k c' d' ⟶ interval k c d' ⊞ K') := by infer_instance
          exact mono_comp _ _
        exact not_mono_biprod_desc hac hac' hce hcd' ι ι' hm
    -- so `K ≅ M_{c,e}`
    refine ⟨c, hac, hce, ?_⟩
    set e₂ : (K : Statement.LinRep k n) ≅ interval k c e := e' ≪≫ (isoBiprodZero hK'z).symm with he₂
    have hcomm' : e₂.inv ≫ K.arrow = ι := by
      rw [hι, he₂]
      simp [isoBiprodZero]
    have hcomm : e₂.hom ≫ ι = K.arrow := ((Iso.inv_comp_eq _).1 hcomm').symm
    rw [← Subobject.mk_arrow K, ← mk_eq_suffix_of_mono hac hce ι]
    exact Subobject.mk_eq_mk_of_comm _ _ e₂ hcomm
end PretorsionImageClosed.LinearQuiver
