-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.exists_idealSheaf_of_locGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:17.253958+00:00
-- url     : https://prove2.me/submissions/2f2b1ae2-e33b-40f9-85fc-1e837e37e3e2

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Theorems.Thm_ReciprocityTheory_AnForm_R_dsJ_basicOpen
import Theorems.Thm_ReciprocityTheory_AnForm_R_dsK_eq
import Theorems.Thm_ReciprocityTheory_AnForm_R_ds_stalkId_eq_map
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_dsJ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {W : Scheme.{0}} {ι' : Type} (V : ι' → W.Opens)
    (hV : ∀ x : W, ∃ c, x ∈ V c) (g : ∀ c, Γ(W, V c))
    (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c')) :
    ∃ G : W.IdealSheafData, ∀ c (x : W) (hx : x ∈ V c),
      FinalTheorems.stalkId G x = Ideal.span {W.presheaf.germ (V c) x hx (g c)} := by
  refine ⟨⟨fun U => dsJ V g U, fun U f => dsJ_basicOpen hV hg U f, _, rfl⟩, fun c x hx => ?_⟩
  obtain ⟨U', hU', hxU', hsub⟩ := exists_isAffineOpen_mem_and_subset hx
  rw [ds_stalkId_eq_map _ ⟨U', hU'⟩ x hxU']
  change Ideal.map _ (dsJ V g ⟨U', hU'⟩) = _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, ← dsK_eq hg c hx]
    exact (mem_dsJ.1 hf) x hxU'
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hle : U' ≤ V c := hsub
    have hr : W.presheaf.map (homOfLE hle).op (g c) ∈ dsJ V g ⟨U', hU'⟩ := by
      rw [mem_dsJ]
      intro y hy
      rw [dsK_eq hg c (hsub hy)]
      apply Ideal.subset_span
      simp
    have e : W.presheaf.germ U' x hxU' (W.presheaf.map (homOfLE hle).op (g c)) =
        W.presheaf.germ (V c) x hx (g c) := by simp
    rw [← e]
    exact Ideal.mem_map_of_mem _ hr
end ReciprocityTheory.AnForm.R
