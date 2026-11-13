-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.open_quasipoint_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:31:30.707205+00:00
-- url     : https://prove2.me/submissions/f46529d4-97a6-4867-aed2-b6826a51e7b3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_quasipoint_cluster_characterization
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_nonmember_has_disjoint_member
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace


open scoped Topology

universe u v

/-- Proposition 3.8; de Groote, Observables I, PDF p./pp. 49.
-/
theorem solution {M : Type u} [TopologicalSpace M] [LocallyCompactSpace M] [T2Space M]
    (B : StoneSpectrum (Opens M)) :
    ((∀ K : Set M, IsCompact K → ∃ U ∈ B.val, (U : Set M) = Kᶜ) ∧
      ¬ ∃ x : M, LiesOver B x) ∨
    ((∃! x : M, LiesOver B x) ∧
      ¬ (∀ K : Set M, IsCompact K → ∃ U ∈ B.val, (U : Set M) = Kᶜ)) := by
  classical
  have hu := quasipoint_upward_and_meet_closed B.val B.property
  by_cases hb : ∀ K : Set M, IsCompact K → ∃ U ∈ B.val, (U : Set M) = Kᶜ
  · refine Or.inl ⟨hb,?_⟩
    rintro ⟨x,hx⟩
    obtain ⟨K,hK,hKn⟩ := exists_compact_mem_nhds x
    obtain ⟨U,hU,hUc⟩ := hb K hK
    have hh := Set.mem_iInter.mp ((open_quasipoint_cluster_characterization B x).1.mp hx)
      (⟨U,hU⟩ : {U : Opens M // U ∈ B.val})
    rw [hUc,closure_compl] at hh
    exact hh (mem_interior_iff_mem_nhds.mpr hKn)
  · refine Or.inr ⟨?_,hb⟩
    push_neg at hb
    obtain ⟨K,hK,hbad⟩ := hb
    let C : Opens M := ⟨Kᶜ,hK.isClosed.isOpen_compl⟩
    have hCn : C ∉ B.val := fun h => hbad C h rfl
    obtain ⟨V,hV,hVC⟩ := quasipoint_nonmember_has_disjoint_member B.val B.property C hCn
    have hVK : (V : Set M) ⊆ K := by
      intro x hx
      by_contra hn
      have hh : x ∈ (V ⊓ C : Opens M) := ⟨hx,hn⟩
      rw [hVC] at hh
      exact hh
    letI : Nonempty {U : Opens M // U ∈ B.val} := ⟨⟨V,hV⟩⟩
    let T := fun U : {U : Opens M // U ∈ B.val} => closure ((U.val ⊓ V : Opens M) : Set M)
    have hd : Directed (· ⊇ ·) T := by
      intro U W
      obtain ⟨Z,hZ,hZU,hZW⟩ := B.property.1.2.2 U.val U.property W.val W.property
      refine ⟨⟨Z,hZ⟩,closure_mono ?_,closure_mono ?_⟩
      · exact inf_le_inf_right V hZU
      · exact inf_le_inf_right V hZW
    have hn (U : {U : Opens M // U ∈ B.val}) : (T U).Nonempty := by
      apply Set.Nonempty.closure
      apply (Opens.ne_bot_iff_nonempty (U.val ⊓ V)).mp
      intro hz
      exact B.property.1.2.1 (hz ▸ hu.2 U.val U.property V hV)
    have hc (U : {U : Opens M // U ∈ B.val}) : IsCompact (T U) := by
      apply hK.of_isClosed_subset isClosed_closure
      apply closure_minimal _ hK.isClosed
      exact Set.inter_subset_right.trans hVK
    obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      T hd hn hc (fun _ => isClosed_closure)
    have hxI : x ∈ ⋂ U : {U : Opens M // U ∈ B.val}, closure (U.val : Set M) := by
      apply Set.mem_iInter.mpr
      intro U
      exact closure_mono Set.inter_subset_left (Set.mem_iInter.mp hx U)
    have hl := (open_quasipoint_cluster_characterization B x).1.mpr hxI
    refine ⟨x,hl,?_⟩
    intro y hy
    change (⋂ U : {U : Opens M // U ∈ B.val}, closure (U.val : Set M)) = {x} at hl
    have hyI := (open_quasipoint_cluster_characterization B y).1.mp hy
    rw [hl] at hyI
    exact hyI
