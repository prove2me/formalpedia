-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.effCartier_of_stalkId
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:16.753859+00:00
-- url     : https://prove2.me/submissions/5e13663e-04c8-4788-b599-2c94a0de8e58

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Theorems.Thm_ReciprocityTheory_AnForm_R_ds_gen_of_span
import Theorems.Thm_ReciprocityTheory_AnForm_R_ds_spread
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
theorem _root_.solution {W : Scheme.{0}} [IsNoetherian W] (G : W.IdealSheafData)
    (hG : ∀ x : W, ∃ t ∈ nonZeroDivisors (W.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}) :
    FinalTheorems.EffCartier G := by
  intro x
  obtain ⟨U0, hU0, hxU0, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : IsNoetherianRing Γ(W, U0) := IsLocallyNoetherian.component_noetherian ⟨U0, hU0⟩
  obtain ⟨t, ht, hst⟩ := hG x
  letI := (W.presheaf.germ U0 x hxU0).hom.toAlgebra
  haveI := hU0.isLocalization_stalk ⟨x, hxU0⟩
  have hI : (G.ideal ⟨U0, hU0⟩).map (algebraMap Γ(W, U0) (W.presheaf.stalk x)) =
      Ideal.span {t} := by
    rw [← hst, ds_stalkId_eq_map G ⟨U0, hU0⟩ x hxU0]
    rfl
  obtain ⟨y, ⟨h, hh, rfl⟩, c, hyc⟩ := ds_gen_of_span
    ((algebraMap Γ(W, U0) (W.presheaf.stalk x)) '' (G.ideal ⟨U0, hU0⟩ : Set Γ(W, U0))) t ht hI
  have hmap : (G.ideal ⟨U0, hU0⟩).map (algebraMap Γ(W, U0) (W.presheaf.stalk x)) =
      Ideal.span {algebraMap Γ(W, U0) (W.presheaf.stalk x) h} := by
    rw [hI, hyc, Ideal.span_singleton_mul_left_unit c.isUnit]
  have hnzd : algebraMap Γ(W, U0) (W.presheaf.stalk x) h ∈
      nonZeroDivisors (W.presheaf.stalk x) := by
    rw [hyc]
    exact mul_mem c.isUnit.mem_nonZeroDivisors ht
  obtain ⟨σ, hσ, hT⟩ := ds_spread (hU0.primeIdealOf ⟨x, hxU0⟩).asIdeal _ h hh hmap hnzd
  letI := (W.presheaf.map (homOfLE <| W.basicOpen_le σ).op).hom.toAlgebra
  haveI := hU0.isLocalization_basicOpen σ
  obtain ⟨h1, h2⟩ := hT Γ(W, W.basicOpen σ)
  refine ⟨W.affineBasicOpen (U := ⟨U0, hU0⟩) σ, algebraMap Γ(W, U0) Γ(W, W.basicOpen σ) h, ?_, h2, ?_⟩
  · have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (W.presheaf.stalk x)
      (hU0.primeIdealOf ⟨x, hxU0⟩).asIdeal σ).2 hσ
    exact (Scheme.mem_basicOpen W σ x hxU0).2 hu
  · rw [← G.map_ideal_basicOpen ⟨U0, hU0⟩ σ]
    exact h1
end ReciprocityTheory.AnForm.R
