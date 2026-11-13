-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.regularization_homeomorphism
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:38:12.150141+00:00
-- url     : https://prove2.me/submissions/72b5ebac-0b61-42df-b8c1-a46c938279f8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_regularized_base_is_quasipoint
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_regularization_membership
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_extends_to_quasipoint
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace


open scoped Topology

universe u v

/-- Proposition 3.16; de Groote, Observables I, PDF p./pp. 56.
-/
theorem solution {M : Type u} [TopologicalSpace M] :
    ∃ h : StoneSpectrum (Opens M) ≃ₜ StoneSpectrum (RegularOpens M),
      ∀ B, (h B).val = regularizedBase B := by
  classical
  have hid (V : RegularOpens M) : regularizeOpen V.val = V.val := Opens.ext V.property
  let r : Opens M → RegularOpens M := fun U => ⟨regularizeOpen U,by simp [regularizeOpen]⟩
  let f : StoneSpectrum (Opens M) → StoneSpectrum (RegularOpens M) :=
    fun B => ⟨regularizedBase B,regularized_base_is_quasipoint B⟩
  have hv (B : StoneSpectrum (Opens M)) (V : RegularOpens M) :
      V ∈ (f B).val ↔ V.val ∈ B.val := by
    constructor
    · rintro ⟨U,hU,he⟩
      have hh := (quasipoint_regularization_membership B U).mp hU
      rwa [he] at hh
    · intro hV
      exact ⟨V.val,hV,hid V⟩
  have hr (B : StoneSpectrum (Opens M)) (U : Opens M) :
      r U ∈ (f B).val ↔ U ∈ B.val := by
    rw [hv]
    exact (quasipoint_regularization_membership B U).symm
  have hinj : Function.Injective f := by
    intro B C he
    apply Subtype.ext
    ext U
    rw [← hr B U, ← hr C U,he]
  have hsurj : Function.Surjective f := by
    intro C
    let A : Set (Opens M) := Subtype.val '' C.val
    have hA : IsFilterBase A := by
      refine ⟨C.property.1.1.image _,?_,?_⟩
      · rintro ⟨V,hV,hV0⟩
        have hz : V = (⊥ : RegularOpens M) := Subtype.ext hV0
        exact C.property.1.2.1 (hz ▸ hV)
      · rintro _ ⟨V,hV,rfl⟩ _ ⟨W,hW,rfl⟩
        obtain ⟨Z,hZ,hZV,hZW⟩ := C.property.1.2.2 V hV W hW
        exact ⟨Z.val,⟨Z,hZ,rfl⟩,hZV,hZW⟩
    obtain ⟨B,hB,hAB⟩ := filter_base_extends_to_quasipoint A hA
    let Q : StoneSpectrum (Opens M) := ⟨B,hB⟩
    have hsub : C.val ⊆ (f Q).val := by
      intro V hV
      exact (hv Q V).mpr (hAB ⟨V,hV,rfl⟩)
    refine ⟨Q,?_⟩
    apply Subtype.ext
    exact C.property.2 (f Q).val (f Q).property.1 hsub
  let e := Equiv.ofBijective f ⟨hinj,hsurj⟩
  have hc : Continuous f := by
    change @Continuous _ _ _ (TopologicalSpace.generateFrom (Set.range (stoneBasic : RegularOpens M → Set (StoneSpectrum (RegularOpens M))))) f
    apply continuous_generateFrom_iff.mpr
    rintro _ ⟨V,rfl⟩
    have he : f ⁻¹' stoneBasic V = stoneBasic V.val := by
      ext B
      exact hv B V
    rw [he]
    exact isOpen_generateFrom_of_mem ⟨V.val,rfl⟩
  have hci : Continuous e.symm := by
    change @Continuous _ _ _ (TopologicalSpace.generateFrom (Set.range (stoneBasic : Opens M → Set (StoneSpectrum (Opens M))))) e.symm
    apply continuous_generateFrom_iff.mpr
    rintro _ ⟨U,rfl⟩
    have he : e.symm ⁻¹' stoneBasic U = stoneBasic (r U) := by
      ext C
      change U ∈ (e.symm C).val ↔ r U ∈ C.val
      rw [← hr]
      have hh : f (e.symm C) = C := e.apply_symm_apply C
      rw [hh]
    rw [he]
    exact isOpen_generateFrom_of_mem ⟨r U,rfl⟩
  refine ⟨{ e with continuous_toFun := hc, continuous_invFun := hci },?_⟩
  intro B
  rfl
