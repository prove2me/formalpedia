-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.mem_support_iff_stalkId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:35.089536+00:00
-- url     : https://prove2.me/submissions/585ca0ef-da95-4f11-b4bd-57da20ca1446

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Theorems.Thm_ReciprocityTheory_AnForm_R_ds_stalkId_eq_map


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
theorem _root_.solution {W : Scheme.{0}} (G : W.IdealSheafData) (x : W) :
    x ∈ (G.support : Set W) ↔ FinalTheorems.stalkId G x ≠ ⊤ := by
  obtain ⟨U', hU', hxU', -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hxU : x ∈ (⟨U', hU'⟩ : W.affineOpens).1 := hxU'
  refine (Scheme.IdealSheafData.mem_support_iff_of_mem hxU).trans ?_
  rw [Scheme.mem_zeroLocus_iff, ds_stalkId_eq_map G _ x hxU]
  constructor
  · intro h htop
    obtain ⟨f, hf, hu⟩ : ∃ f ∈ G.ideal ⟨U', hU'⟩, IsUnit (W.presheaf.germ U' x hxU' f) := by
      by_contra hno
      push_neg at hno
      have hle : Ideal.map (W.presheaf.germ U' x hxU').hom (G.ideal ⟨U', hU'⟩) ≤
          IsLocalRing.maximalIdeal _ := by
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        exact (IsLocalRing.mem_maximalIdeal _).2 (hno f hf)
      rw [htop] at hle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 hle)
    exact h f hf ((Scheme.mem_basicOpen _ _ _ _).2 hu)
  · intro h f hf hxf
    apply h
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
      ((Scheme.mem_basicOpen _ _ _ hxU).1 hxf)
end ReciprocityTheory.AnForm.R
