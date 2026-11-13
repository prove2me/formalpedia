-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.borel_saturation_quasipoint
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T03:02:46.685205+00:00
-- url     : https://prove2.me/submissions/31864935-ef56-456d-b1a1-18eba4d93b69

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
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

/-- Proposition 3.17; de Groote, Observables I, PDF p./pp. 57.
-/
theorem solution {M : Type u} [TopologicalSpace M] [BaireSpace M]
    (B : StoneSpectrum (Opens M)) :
    IsQuasipoint (borelSaturation B) ∧
      ∀ A ∈ borelSaturation B, ¬ IsMeagre A.val := by
  classical
  borelize M
  have hrel (A U : Set M) : IsMeagre ((A \ U) ∪ (U \ A)) ↔ A =ᵇ U := by
    rw [Filter.eventuallyEq_set]
    change ((A \ U) ∪ (U \ A))ᶜ ∈ residual M ↔ {x | x ∈ A ↔ x ∈ U} ∈ residual M
    have he : ((A \ U) ∪ (U \ A))ᶜ = {x | x ∈ A ↔ x ∈ U} := by
      ext x
      simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_diff,Set.mem_setOf_eq]
      tauto
    rw [he]
  have hu := quasipoint_upward_and_meet_closed B.val B.property
  have hnm (A : BorelSets M) (hA : A ∈ borelSaturation B) : ¬ IsMeagre A.val := by
    rintro hm
    obtain ⟨U,hU,hAU⟩ := hA
    have hme : IsMeagre (U : Set M) := (hm.union hAU).mono (by
      intro x hx
      by_cases ha : x ∈ A.val
      · exact Or.inl ha
      · exact Or.inr (Or.inr ⟨hx,ha⟩))
    have hn : (U : Set M).Nonempty := (Opens.ne_bot_iff_nonempty U).mp
      (fun hz => B.property.1.2.1 (hz ▸ hU))
    exact not_isMeagre_of_isOpen U.isOpen hn hme
  have hb : IsFilterBase (borelSaturation B) := by
    refine ⟨?_,?_,?_⟩
    · obtain ⟨U,hU⟩ := B.property.1.1
      exact ⟨⟨(U : Set M),U.isOpen.measurableSet⟩,U,hU,(hrel _ _).mpr Filter.EventuallyEq.rfl⟩
    · intro hh
      exact hnm ⊥ hh IsMeagre.empty
    · rintro A ⟨U,hU,hAU⟩ C ⟨V,hV,hCV⟩
      refine ⟨A ⊓ C,⟨U ⊓ V,hu.2 U hU V hV,(hrel _ _).mpr ?_⟩,inf_le_left,inf_le_right⟩
      exact ((hrel _ _).mp hAU).inter ((hrel _ _).mp hCV)
  refine ⟨⟨hb,?_⟩,hnm⟩
  intro C hC hBC
  apply Set.Subset.antisymm _ hBC
  intro A hAC
  obtain ⟨U,hU,hAU⟩ := A.property.residualEq_isOpen
  let V : Opens M := ⟨U,hU⟩
  by_cases hV : V ∈ B.val
  · exact ⟨V,hV,(hrel _ _).mpr hAU⟩
  · obtain ⟨W,hW,hWV⟩ := quasipoint_nonmember_has_disjoint_member B.val B.property V hV
    let D : BorelSets M := ⟨(W : Set M) \ A.val,W.isOpen.measurableSet.diff A.property⟩
    have he : (W : Set M) \ U = (W : Set M) := by
      ext x
      constructor
      · exact fun h => h.1
      · intro hx
        refine ⟨hx,?_⟩
        intro hxU
        have hh : x ∈ (W ⊓ V : Opens M) := ⟨hx,hxU⟩
        rw [hWV] at hh
        exact hh
    have hDW : D.val =ᵇ (W : Set M) := by
      have hh := (Filter.EventuallyEq.rfl (l := residual M) (f := (W : Set M))).diff hAU
      rwa [he] at hh
    have hD : D ∈ C := hBC ⟨W,hW,(hrel _ _).mpr hDW⟩
    obtain ⟨Z,hZ,hZA,hZD⟩ := hC.2.2 A hAC D hD
    have hz : Z = ⊥ := by
      apply Subtype.ext
      ext x
      change x ∈ Z.val ↔ False
      exact ⟨fun hx => (hZD hx).2 (hZA hx),False.elim⟩
    exact False.elim (hC.2.1 (hz ▸ hZ))
