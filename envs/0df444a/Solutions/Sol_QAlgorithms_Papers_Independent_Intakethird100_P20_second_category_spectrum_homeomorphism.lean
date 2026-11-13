-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.second_category_spectrum_homeomorphism
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T03:15:50.955969+00:00
-- url     : https://prove2.me/submissions/f5c12e0c-f76d-415b-984b-435abe7744e4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_borel_saturation_quasipoint
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_extends_to_quasipoint
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_nonmember_has_disjoint_member
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.Lemmas
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace


open scoped Topology

universe u v

/-- Proposition 3.18; de Groote, Observables I, PDF p./pp. 58.
-/
theorem solution {M : Type u} [TopologicalSpace M] [BaireSpace M] :
    ∃ h : StoneSpectrum (Opens M) ≃ₜ
      {C : StoneSpectrum (BorelSets M) // ∀ A ∈ C.val, ¬ IsMeagre A.val},
      ∀ B, (h B).val.val = borelSaturation B := by
  classical
  borelize M
  let φ : Opens M → BorelSets M := fun U => ⟨(U : Set M),U.isOpen.measurableSet⟩
  have hrel (A U : Set M) : IsMeagre ((A \ U) ∪ (U \ A)) ↔ A =ᵇ U := by
    rw [Filter.eventuallyEq_set]
    change ((A \ U) ∪ (U \ A))ᶜ ∈ residual M ↔ {x | x ∈ A ↔ x ∈ U} ∈ residual M
    have he : ((A \ U) ∪ (U \ A))ᶜ = {x | x ∈ A ↔ x ∈ U} := by
      ext x
      simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_diff,Set.mem_setOf_eq]
      tauto
    rw [he]
  have hos (B : StoneSpectrum (Opens M)) (V U : Opens M)
      (hVU : (V : Set M) =ᵇ (U : Set M)) (hV : V ∈ B.val) : U ∈ B.val := by
    by_contra hn
    obtain ⟨W,hW,hWU⟩ := quasipoint_nonmember_has_disjoint_member B.val B.property U hn
    have hi := (quasipoint_upward_and_meet_closed B.val B.property).2 V hV W hW
    have hne : ((V ⊓ W : Opens M) : Set M).Nonempty :=
      (Opens.ne_bot_iff_nonempty (V ⊓ W)).mp (fun hz => B.property.1.2.1 (hz ▸ hi))
    have hm : IsMeagre ((V : Set M) \ (U : Set M)) :=
      ((hrel _ _).mpr hVU).mono Set.subset_union_left
    apply not_isMeagre_of_isOpen (V ⊓ W).isOpen hne
    apply hm.mono
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hxU
    have hh : x ∈ (W ⊓ U : Opens M) := ⟨hx.2,hxU⟩
    rw [hWU] at hh
    exact hh
  have hmem (B : StoneSpectrum (Opens M)) (A : BorelSets M) (U : Opens M)
      (hAU : A.val =ᵇ (U : Set M)) : A ∈ borelSaturation B ↔ U ∈ B.val := by
    constructor
    · rintro ⟨V,hV,hAV⟩
      exact hos B V U (((hrel _ _).mp hAV).symm.trans hAU) hV
    · intro hU
      exact ⟨U,hU,(hrel _ _).mpr hAU⟩
  let S := {C : StoneSpectrum (BorelSets M) // ∀ A ∈ C.val, ¬ IsMeagre A.val}
  let f : StoneSpectrum (Opens M) → S := fun B =>
    ⟨⟨borelSaturation B,(borel_saturation_quasipoint B).1⟩,(borel_saturation_quasipoint B).2⟩
  have hs (C : S) (A D : BorelSets M) (hAD : A.val =ᵇ D.val)
      (hA : A ∈ C.val.val) : D ∈ C.val.val := by
    by_contra hn
    obtain ⟨E,hE,hED⟩ := quasipoint_nonmember_has_disjoint_member C.val.val C.val.property D hn
    have hu := quasipoint_upward_and_meet_closed C.val.val C.val.property
    have hAE := hu.2 A hA E hE
    apply C.property (A ⊓ E) hAE
    have hm : IsMeagre (A.val \ D.val) := ((hrel _ _).mpr hAD).mono Set.subset_union_left
    apply hm.mono
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hxD
    have hh : x ∈ (E ⊓ D).val := ⟨hx.2,hxD⟩
    rw [hED] at hh
    exact hh
  have hinj : Function.Injective f := by
    intro B D he
    have hv : borelSaturation B = borelSaturation D := congrArg (fun C : S => C.val.val) he
    apply Subtype.ext
    ext U
    rw [← hmem B (φ U) U Filter.EventuallyEq.rfl,← hmem D (φ U) U Filter.EventuallyEq.rfl,hv]
  have hsurj : Function.Surjective f := by
    intro C
    have hu := quasipoint_upward_and_meet_closed C.val.val C.val.property
    let J : Set (Opens M) := {U | φ U ∈ C.val.val}
    have htop : (⊤ : BorelSets M) ∈ C.val.val := by
      obtain ⟨A,hA⟩ := C.val.property.1.1
      exact hu.1 A hA ⊤ le_top
    have hJ : IsFilterBase J := by
      refine ⟨⟨⊤,htop⟩,C.val.property.1.2.1,?_⟩
      intro U hU V hV
      exact ⟨U ⊓ V,hu.2 (φ U) hU (φ V) hV,inf_le_left,inf_le_right⟩
    obtain ⟨B,hB,hJB⟩ := filter_base_extends_to_quasipoint J hJ
    let Q : StoneSpectrum (Opens M) := ⟨B,hB⟩
    have hsub : C.val.val ⊆ borelSaturation Q := by
      intro A hA
      obtain ⟨U,hU,hAU⟩ := A.property.residualEq_isOpen
      let V : Opens M := ⟨U,hU⟩
      have hV : φ V ∈ C.val.val := hs C A (φ V) hAU hA
      exact (hmem Q A V hAU).mpr (hJB hV)
    refine ⟨Q,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact C.val.property.2 (borelSaturation Q) (borel_saturation_quasipoint Q).1.1 hsub
  let e := Equiv.ofBijective f ⟨hinj,hsurj⟩
  have h0 : Continuous (fun B => (f B).val) := by
    change @Continuous _ _ _ (TopologicalSpace.generateFrom
      (Set.range (stoneBasic : BorelSets M → Set (StoneSpectrum (BorelSets M))))) (fun B => (f B).val)
    apply continuous_generateFrom_iff.mpr
    rintro _ ⟨A,rfl⟩
    obtain ⟨U,hU,hAU⟩ := A.property.residualEq_isOpen
    let V : Opens M := ⟨U,hU⟩
    have he : (fun B => (f B).val) ⁻¹' stoneBasic A = stoneBasic V := by
      ext B
      exact hmem B A V hAU
    rw [he]
    exact isOpen_generateFrom_of_mem ⟨V,rfl⟩
  have hc : Continuous f := h0.subtype_mk _
  have hci : Continuous e.symm := by
    change @Continuous _ _ _ (TopologicalSpace.generateFrom
      (Set.range (stoneBasic : Opens M → Set (StoneSpectrum (Opens M))))) e.symm
    apply continuous_generateFrom_iff.mpr
    rintro _ ⟨U,rfl⟩
    have he : e.symm ⁻¹' stoneBasic U = (Subtype.val : S → StoneSpectrum (BorelSets M)) ⁻¹' stoneBasic (φ U) := by
      ext C
      change U ∈ (e.symm C).val ↔ φ U ∈ C.val.val
      rw [← hmem (e.symm C) (φ U) U Filter.EventuallyEq.rfl]
      have hh : f (e.symm C) = C := e.apply_symm_apply C
      change φ U ∈ (f (e.symm C)).val.val ↔ φ U ∈ C.val.val
      rw [hh]
    rw [he]
    have hOpen : IsOpen (stoneBasic (φ U) : Set (StoneSpectrum (BorelSets M))) :=
      isOpen_generateFrom_of_mem ⟨φ U,rfl⟩
    exact hOpen.preimage continuous_subtype_val
  refine ⟨{ e with continuous_toFun := hc,continuous_invFun := hci },?_⟩
  intro B
  rfl
