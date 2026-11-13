-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.regularized_base_is_quasipoint
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:36:46.004771+00:00
-- url     : https://prove2.me/submissions/d0c05500-ced3-431c-9387-b43efa67773a

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_regularization_preserves_meet
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_regularization_membership
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace


open scoped Topology

universe u v

/-- Lemma 3.4; de Groote, Observables I, PDF p./pp. 56.
-/
theorem solution {M : Type u} [TopologicalSpace M] (B : StoneSpectrum (Opens M)) :
    IsQuasipoint (regularizedBase B) := by
  classical
  have hm (U V : Opens M) (h : U ≤ V) : regularizeOpen U ≤ regularizeOpen V :=
    interior_mono (closure_mono h)
  have hself (U : Opens M) : U ≤ regularizeOpen U := U.isOpen.subset_interior_closure
  have hid (V : RegularOpens M) : regularizeOpen V.val = V.val := Opens.ext V.property
  let r : Opens M → RegularOpens M := fun U => ⟨regularizeOpen U,by simp [regularizeOpen]⟩
  have hr (U : Opens M) : r U ∈ regularizedBase B ↔ U ∈ B.val := by
    constructor
    · rintro ⟨V,hV,hVU⟩
      apply (quasipoint_regularization_membership B U).mpr
      change regularizeOpen V = regularizeOpen U at hVU
      rw [← hVU]
      exact (quasipoint_regularization_membership B V).mp hV
    · intro hU; exact ⟨U,hU,rfl⟩
  have hb : IsFilterBase (regularizedBase B) := by
    refine ⟨?_,?_,?_⟩
    · obtain ⟨U,hU⟩ := B.property.1.1
      exact ⟨r U,(hr U).mpr hU⟩
    · rintro ⟨U,hU,he⟩
      have hz : U = ⊥ := le_bot_iff.mp (by
        have hh := hself U
        have he' : regularizeOpen U = ⊥ := he
        rwa [he'] at hh)
      exact B.property.1.2.1 (hz ▸ hU)
    · rintro V ⟨U,hU,hUV⟩ W ⟨T,hT,hTW⟩
      have hUT := (quasipoint_upward_and_meet_closed B.val B.property).2 U hU T hT
      refine ⟨r (U ⊓ T),(hr _).mpr hUT,?_,?_⟩
      · change regularizeOpen (U ⊓ T) ≤ V.val
        rw [← hUV]
        exact hm _ _ inf_le_left
      · change regularizeOpen (U ⊓ T) ≤ W.val
        rw [← hTW]
        exact hm _ _ inf_le_right
  refine ⟨hb,?_⟩
  intro C hC hBC
  let D : Set (Opens M) := {U | ∃ V ∈ C, V.val ≤ regularizeOpen U}
  have hD : IsFilterBase D := by
    refine ⟨?_,?_,?_⟩
    · obtain ⟨V,hV⟩ := hC.1
      exact ⟨V.val,V,hV,by rw [hid]⟩
    · rintro ⟨V,hV,hV0⟩
      have hz : V = ⊥ := by
        apply Subtype.ext
        exact le_bot_iff.mp (by simpa [regularizeOpen] using hV0)
      exact hC.2.1 (hz ▸ hV)
    · rintro U ⟨V,hV,hVU⟩ T ⟨W,hW,hWT⟩
      obtain ⟨Z,hZ,hZV,hZW⟩ := hC.2.2 V hV W hW
      refine ⟨U ⊓ T,⟨Z,hZ,?_⟩,inf_le_left,inf_le_right⟩
      rw [regularization_preserves_meet]
      exact le_inf (le_trans hZV hVU) (le_trans hZW hWT)
  have hBD : B.val ⊆ D := by
    intro U hU
    exact ⟨r U,hBC ((hr U).mpr hU),le_rfl⟩
  have heq := B.property.2 D hD hBD
  apply Set.Subset.antisymm _ hBC
  intro V hV
  have hd : V.val ∈ D := ⟨V,hV,by rw [hid]⟩
  have hvB : V.val ∈ B.val := heq ▸ hd
  exact ⟨V.val,hvB,hid V⟩
