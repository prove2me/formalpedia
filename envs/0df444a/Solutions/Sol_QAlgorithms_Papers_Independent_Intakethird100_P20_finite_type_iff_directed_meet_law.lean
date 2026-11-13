-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.finite_type_iff_directed_meet_law
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:24:54.592355+00:00
-- url     : https://prove2.me/submissions/ec6520c7-8b2f-4a4f-91ee-b6d48af2b0ee

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stone_topology_properties
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthomodular_basic_sets_injective
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_basic_union_closure_of_meet_distribution
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 3.2; de Groote, Observables I, PDF p./pp. 46.
-/
theorem solution {L : Type u} [CompleteLattice L] (perp : L → L) (horth : IsOrthomodular perp) :
    IsFiniteType L ↔ HasDirectedMeetLaw L := by
  classical
  have ht := stone_topology_properties (L := L)
  have hm := ht.1
  constructor
  · intro hf a s hs hd
    let t : Set L := (fun b => a ⊓ b) '' s
    have htn : t.Nonempty := hs.image _
    have htd : DirectedOn (· ≤ ·) t := by
      rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
      obtain ⟨d, hds, hbd, hcd⟩ := hd b hb c hc
      exact ⟨a ⊓ d, ⟨d, hds, rfl⟩, inf_le_inf_left a hbd, inf_le_inf_left a hcd⟩
    have hct := hf t htn htd
    have hcs := hf s hs hd
    let U := ⋃ b ∈ s, stoneBasic b
    have hcl : closure (stoneBasic a ∩ U) = stoneBasic a ∩ closure U := by
      apply Set.Subset.antisymm
      · simpa only [(ht.2.2.2.1 a).1.closure_eq] using
          (closure_inter_subset : closure (stoneBasic a ∩ U) ⊆ closure (stoneBasic a) ∩ closure U)
      · exact (ht.2.2.2.1 a).2.inter_closure
    have hunion : (⋃ c ∈ t, stoneBasic c) = stoneBasic a ∩ U := by
      simp only [t, U, Set.biUnion_image, hm, Set.inter_iUnion]
    apply orthomodular_basic_sets_injective perp horth
    calc
      stoneBasic (a ⊓ sSup s) = stoneBasic a ∩ stoneBasic (sSup s) := hm a (sSup s)
      _ = stoneBasic a ∩ closure U := by rw [show closure U = stoneBasic (sSup s) from hcs]
      _ = closure (stoneBasic a ∩ U) := hcl.symm
      _ = closure (⋃ c ∈ t, stoneBasic c) := congrArg closure hunion.symm
      _ = stoneBasic (sSup t) := hct
  · intro hd s hs hdir
    exact basic_union_closure_of_meet_distribution s (fun a => hd a s hs hdir)
