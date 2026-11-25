-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_exists_etaleChart_comap_subscheme__eraseIdx_fdb03de3c0d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:48:53.841356+00:00
-- url     : https://prove2.me/submissions/ad5f8a1e-d006-4e70-ba7e-66cee2841417

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_StrictNormalCrossingsEraseMember
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_restrictToSubscheme_coordIdeal_singleton
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_restrict_coordIdeal_of_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_top_of_le
import Theorems.Thm_P2M_AlgebraicGeometry_Scheme_IdealSheafData_notMem_support_of_comap___eq_top_c656226848a8
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_comap_subscheme__eq_top_6abe0cb72e4b
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def


section
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem natSuccAbove_ne (j i : ℕ) : natSuccAbove j i ≠ j := by
  unfold natSuccAbove
  split_ifs with h <;> omega
private theorem natSuccAbove_inj (j i i' : ℕ) (h : natSuccAbove j i = natSuccAbove j i') : i = i' := by
  unfold natSuccAbove at h
  split_ifs at h <;> omega
private theorem getElem_eraseIdx_natSuccAbove {α : Type u} (l : List α) (j i : ℕ)
    (hi : i < (l.eraseIdx j).length) (hs : natSuccAbove j i < l.length) :
    (l.eraseIdx j)[i]'hi = l[natSuccAbove j i]'hs := by
  unfold natSuccAbove at hs ⊢
  rw [List.getElem_eraseIdx]
  split <;> simp [*]
private theorem mem_of_complOrderEmbPreimage_eq_none (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (h : complOrderEmbPreimage m S s = none) : s ∈ S := by
  by_contra hs
  unfold complOrderEmbPreimage at h
  rw [dif_neg hs] at h
  simp at h
private theorem complOrderEmb_of_complOrderEmbPreimage_eq_some (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (u : Fin (m - S.card)) (h : complOrderEmbPreimage m S s = some u) : complOrderEmb m S u = s := by
  by_cases hs : s ∈ S
  · exfalso
    unfold complOrderEmbPreimage at h
    rw [dif_pos hs] at h
    simp at h
  · unfold complOrderEmbPreimage at h
    rw [dif_neg hs] at h
    have hu : Classical.choose (exists_complOrderEmb_eq m S hs) = u := Option.some.inj h
    rw [← hu]
    exact Classical.choose_spec (exists_complOrderEmb_eq m S hs)
private theorem transportSuccAboveToCompl_eq_some {m : ℕ} (S : Finset (Fin m)) (j : ℕ)
    (a : ℕ → Option (Fin m)) (i : ℕ) (u : Fin (m - S.card))
    (h : transportSuccAboveToCompl S j a i = some u) : a (natSuccAbove j i) = some (complOrderEmb m S u) := by
  rcases hs : a (natSuccAbove j i) with _ | s
  · exfalso
    unfold transportSuccAboveToCompl at h
    rw [hs] at h
    simp at h
  · have h' : complOrderEmbPreimage m S s = some u := by
      unfold transportSuccAboveToCompl at h
      rw [hs] at h
      exact h
    rw [complOrderEmb_of_complOrderEmbPreimage_eq_some m S s u h']
private theorem transportSuccAboveToCompl_eq_none {m : ℕ} (S : Finset (Fin m)) (j : ℕ)
    (a : ℕ → Option (Fin m)) (i : ℕ) (h : transportSuccAboveToCompl S j a i = none) :
    a (natSuccAbove j i) = none ∨ ∃ s, a (natSuccAbove j i) = some s ∧ s ∈ S := by
  rcases hs : a (natSuccAbove j i) with _ | s
  · exact Or.inl rfl
  · refine Or.inr ⟨s, rfl, ?_⟩
    have h' : complOrderEmbPreimage m S s = none := by
      unfold transportSuccAboveToCompl at h
      rw [hs] at h
      exact h
    exact mem_of_complOrderEmbPreimage_eq_none m S s h'
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (j : ℕ) (hj : j < E.length) (z : ↥((E[j]'hj).subscheme)) :
    ∃ (U : ((E[j]'hj).subscheme).Opens) (_ : z ∈ U) (m : ℕ)
      (c : EtaleChart ((E[j]'hj).subschemeι ≫ p) U m) (a : ℕ → Option (Fin m)),
      (∀ i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length,
        ∀ i' < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length,
        ∀ t : Fin m, a i = some t → a i' = some t → i = i') ∧
      (∀ (i : ℕ) (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length),
        a i = none →
          restrictIdeal (((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]) U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length)
        (t : Fin m), a i = some t →
          restrictIdeal (((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]) U =
            c.coordIdeal {t}) := by
  classical
  obtain ⟨-, hpos⟩ := (inStrictNormalCrossingPosition_iff p E).mp hE
  have hx : (E[j]'hj).subschemeι.base z ∈ (E[j]'hj).support := by
    have hmem : (E[j]'hj).subschemeι.base z ∈ Set.range (E[j]'hj).subschemeι.base :=
      Set.mem_range_self z
    simpa using hmem
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := (hpos ((E[j]'hj).subschemeι.base z)).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU
  have hV : IsAffineOpen V := hVB
  rcases haj : a j with _ | t
  · refine absurd hx ?_
    refine AlgebraicGeometry.Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ ?_ hxU
    rw [← restrictIdeal_eq_comap_ι]
    exact h2 j hj haj
  · have hzmem : z ∈ (E[j]'hj).subschemeι ⁻¹ᵁ V := hxV
    have h2V : ∀ (i : ℕ) (hi : i < E.length), a i = none → restrictIdeal (E[i]'hi) V = ⊤ :=
      fun i hi hn => restrictIdeal_eq_top_of_le _ hVU (h2 i hi hn)
    have h3V : ∀ (i : ℕ) (hi : i < E.length) (s : Fin m), a i = some s →
        restrictIdeal (E[i]'hi) V = (c.restrict hVU).coordIdeal {s} :=
      fun i hi s hsm => restrictIdeal_eq_restrict_coordIdeal_of_le hVU c (E[i]'hi) {s} (h3 i hi s hsm)
    have hZV : restrictIdeal (E[j]'hj) V = (c.restrict hVU).coordIdeal {t} := h3V j hj t haj
    have hlen : ∀ i, i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length →
        natSuccAbove j i < E.length := by
      intro i hi
      rw [List.length_map] at hi
      have h0 := List.length_eraseIdx_add_one hj
      unfold natSuccAbove
      split_ifs with hc <;> omega
    have helem : ∀ (i : ℕ)
        (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length),
        ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]'hi =
          (E[natSuccAbove j i]'(hlen i hi)).comap (E[j]'hj).subschemeι := by
      intro i hi
      have hi' : i < (E.eraseIdx j).length := by
        rw [List.length_map] at hi
        exact hi
      have he : (E.eraseIdx j)[i]'hi' = E[natSuccAbove j i]'(hlen i hi) :=
        getElem_eraseIdx_natSuccAbove E j i hi' (hlen i hi)
      rw [List.getElem_map]
      exact congrArg (fun D => D.comap (E[j]'hj).subschemeι) he
    refine ⟨(E[j]'hj).subschemeι ⁻¹ᵁ V, hzmem, m - ({t} : Finset (Fin m)).card,
      (c.restrict hVU).restrictToSubscheme hV (E[j]'hj) {t} hZV,
      transportSuccAboveToCompl {t} j a, ?_, ?_, ?_⟩
    · intro i hi i' hi' u hu hu'
      exact natSuccAbove_inj j i i'
        (h1 (natSuccAbove j i) (hlen i hi) (natSuccAbove j i') (hlen i' hi')
          (complOrderEmb m {t} u) (transportSuccAboveToCompl_eq_some {t} j a i u hu)
          (transportSuccAboveToCompl_eq_some {t} j a i' u hu'))
    · intro i hi hn
      rw [helem i hi]
      rcases transportSuccAboveToCompl_eq_none {t} j a i hn with hnone | ⟨s, hsome, hsmem⟩
      · exact restrictIdeal_comap_subschemeι_eq_top (E[j]'hj) V _
          (h2V (natSuccAbove j i) (hlen i hi) hnone)
      · exfalso
        have h0 : a (natSuccAbove j i) = some t := by
          rw [hsome, Finset.mem_singleton.mp hsmem]
        exact natSuccAbove_ne j i (h1 (natSuccAbove j i) (hlen i hi) j hj t h0 haj)
    · intro i hi u hu
      rw [helem i hi]
      exact (c.restrict hVU).restrictToSubscheme_coordIdeal_singleton hV (E[j]'hj) {t} hZV u
        (E[natSuccAbove j i]'(hlen i hi))
        (h3V (natSuccAbove j i) (hlen i hi) (complOrderEmb m {t} u)
          (transportSuccAboveToCompl_eq_some {t} j a i u hu))
end FunctorialResolution.EmbeddedResolution
