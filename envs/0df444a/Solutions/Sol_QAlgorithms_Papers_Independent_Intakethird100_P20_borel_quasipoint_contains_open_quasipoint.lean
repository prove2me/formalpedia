-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.borel_quasipoint_contains_open_quasipoint
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T03:13:43.627184+00:00
-- url     : https://prove2.me/submissions/b2446d27-2c80-4500-bf8a-b613ae34a536

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_nonmember_has_disjoint_member
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_dual_ideal_quasipoint_alternative
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_distributive_basic_unions
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace


open scoped Topology

universe u v

/-- Proposition 3.19; de Groote, Observables I, PDF p./pp. 59.
-/
theorem solution {M : Type u} [TopologicalSpace M] [BaireSpace M]
    (C : StoneSpectrum (BorelSets M)) :
    (∃ B : StoneSpectrum (Opens M), ∀ U ∈ B.val, ∃ A ∈ C.val, A.val = (U : Set M)) ↔
    ∀ U : Opens M, ¬ ∃ A ∈ C.val, A.val = closure (U : Set M) \ (U : Set M) := by
  classical
  borelize M
  let φ : Opens M → BorelSets M := fun U => ⟨(U : Set M),U.isOpen.measurableSet⟩
  have hu := quasipoint_upward_and_meet_closed C.val C.property
  constructor
  · rintro ⟨B,hBC⟩ U ⟨A,hA,hAe⟩
    have hb := quasipoint_upward_and_meet_closed B.val B.property
    have hJ : IsDualIdeal B.val := ⟨B.property.1.1,B.property.1.2.1,hb.1,hb.2⟩
    have avoid (W : Opens M) (hW : W ∈ B.val)
        (hd : ∀ x, x ∈ closure (U : Set M) \ (U : Set M) → x ∈ (W : Set M) → False) : False := by
      obtain ⟨E,hE,hEW⟩ := hBC W hW
      obtain ⟨Z,hZ,hZA,hZE⟩ := C.property.1.2.2 A hA E hE
      have hz : Z = ⊥ := by
        apply Subtype.ext
        ext x
        change x ∈ Z.val ↔ False
        refine ⟨fun hx => ?_,False.elim⟩
        have hxA := hZA hx
        rw [hAe] at hxA
        have hxE := hZE hx
        rw [hEW] at hxE
        exact hd x hxA hxE
      exact C.property.1.2.1 (hz ▸ hZ)
    rcases (open_dual_ideal_quasipoint_alternative B.val hJ).mp B.property U with hU | hUc
    · exact avoid U hU (fun x hx hxU => hx.2 hxU)
    · apply avoid (openPseudoCompl U) hUc
      intro x hx hxc
      exact hxc hx.1
  · intro hboundary
    have hd : IsDistributive (L := BorelSets M) := by
      constructor
      · intro A B D
        apply Subtype.ext
        ext x
        change (x ∈ A.val ∧ (x ∈ B.val ∨ x ∈ D.val)) ↔
          ((x ∈ A.val ∧ x ∈ B.val) ∨ (x ∈ A.val ∧ x ∈ D.val))
        tauto
      · intro A B D
        apply Subtype.ext
        ext x
        change (x ∈ A.val ∨ (x ∈ B.val ∧ x ∈ D.val)) ↔
          ((x ∈ A.val ∨ x ∈ B.val) ∧ (x ∈ A.val ∨ x ∈ D.val))
        tauto
    have hprime (A D : BorelSets M) (hAD : A ⊔ D ∈ C.val) : A ∈ C.val ∨ D ∈ C.val := by
      change C ∈ stoneBasic A ∪ stoneBasic D
      rw [distributive_basic_unions.1 hd]
      exact hAD
    let J : Set (Opens M) := {U | φ U ∈ C.val}
    have htop : (⊤ : BorelSets M) ∈ C.val := by
      obtain ⟨A,hA⟩ := C.property.1.1
      exact hu.1 A hA ⊤ le_top
    have hJ : IsDualIdeal J := by
      refine ⟨⟨⊤,htop⟩,C.property.1.2.1,?_,?_⟩
      · intro U hU V hUV
        exact hu.1 (φ U) hU (φ V) hUV
      · intro U hU V hV
        exact hu.2 (φ U) hU (φ V) hV
    have hq : IsQuasipoint J := by
      apply (open_dual_ideal_quasipoint_alternative J hJ).mpr
      intro U
      let D : BorelSets M := ⟨closure (U : Set M) \ (U : Set M),
        isClosed_closure.measurableSet.diff U.isOpen.measurableSet⟩
      have hn : D ∉ C.val := fun hD => hboundary U ⟨D,hD,rfl⟩
      obtain ⟨E,hE,hED⟩ := quasipoint_nonmember_has_disjoint_member C.val C.property D hn
      let Dc : BorelSets M := ⟨D.valᶜ,D.property.compl⟩
      have hsub : E ≤ Dc := by
        intro x hx hxD
        have hh : x ∈ (E ⊓ D).val := ⟨hx,hxD⟩
        rw [hED] at hh
        exact hh
      have hDc := hu.1 E hE Dc hsub
      have he : φ U ⊔ φ (openPseudoCompl U) = Dc := by
        apply Subtype.ext
        ext x
        change (x ∈ (U : Set M) ∨ x ∉ closure (U : Set M)) ↔
          ¬ (x ∈ closure (U : Set M) ∧ x ∉ (U : Set M))
        tauto
      have hh : φ U ⊔ φ (openPseudoCompl U) ∈ C.val := he ▸ hDc
      exact hprime _ _ hh
    exact ⟨⟨J,hq⟩,fun U hU => ⟨φ U,hU,rfl⟩⟩
