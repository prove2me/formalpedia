-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.heyting_stone_compact
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:51:41.418848+00:00
-- url     : https://prove2.me/submissions/52dc1d74-3f02-4bf3-a30d-38f1ba10241b

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_nonmember_has_disjoint_member
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_filter_base_extends_to_quasipoint
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace
open scoped Topology

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {L : Type*} [HeytingAlgebra L] :
    CompactSpace (StoneSpectrum L) := by
  classical
  have ht := stone_topology_properties (L := L)
  have hu := quasipoint_upward_and_meet_closed (L := L)
  have hcomp (a : L) : stoneBasic aᶜ = (stoneBasic a)ᶜ := by
    ext B
    change (aᶜ ∈ B.val) ↔ a ∉ B.val
    constructor
    · intro hc ha
      have hz := (hu B.val B.property).2 a ha aᶜ hc
      rw [inf_compl_eq_bot] at hz
      exact B.property.1.2.1 hz
    · intro ha
      obtain ⟨b, hb, hba⟩ := quasipoint_nonmember_has_disjoint_member B.val B.property a ha
      exact (hu B.val B.property).1 b hb aᶜ
        (le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr hba))
  constructor
  apply isCompact_iff_ultrafilter_le_nhds'.mpr
  intro F _
  let J : Set L := {a | stoneBasic a ∈ F}
  have hJ : IsFilterBase J := by
    refine ⟨⟨⊤, ?_⟩, ?_, ?_⟩
    · change stoneBasic (⊤ : L) ∈ F
      rw [ht.2.2.1]
      exact Filter.univ_mem
    · intro hbot
      change stoneBasic (⊥ : L) ∈ F at hbot
      rw [ht.2.1] at hbot
      exact F.empty_notMem hbot
    · intro a ha b hb
      refine ⟨a ⊓ b, ?_, inf_le_left, inf_le_right⟩
      change stoneBasic (a ⊓ b) ∈ F
      rw [ht.1]
      exact Filter.inter_mem ha hb
  obtain ⟨P, hP, hJP⟩ := filter_base_extends_to_quasipoint J hJ
  let B : StoneSpectrum L := ⟨P, hP⟩
  refine ⟨B, Set.mem_univ B, ?_⟩
  intro U hU
  obtain ⟨_, ⟨a, rfl⟩, haB, hsub⟩ := ht.2.2.2.2.1.mem_nhds_iff.mp hU
  apply Filter.mem_of_superset _ hsub
  by_contra haF
  have hcF : stoneBasic aᶜ ∈ F := by
    rw [hcomp]
    exact F.compl_mem_iff_notMem.mpr haF
  have hca : aᶜ ∈ P := hJP hcF
  have hz := (hu P hP).2 a haB aᶜ hca
  rw [inf_compl_eq_bot] at hz
  exact hP.1.2.1 hz
