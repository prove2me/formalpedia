-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.stone_topology_properties
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T16:00:31.650064+00:00
-- url     : https://prove2.me/submissions/56577d07-90b9-41f1-9905-4c40ba8d84f3

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_nonmember_has_disjoint_member
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open QAlgorithms.Papers.Independent.Intakethird100.P20
noncomputable section



open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- stone-topology-properties; de Groote, Observables I, PDF p./pp. 40.
-/
theorem solution {L : Type u} [Lattice L] [BoundedOrder L] :
    (∀ a b : L, stoneBasic (a ⊓ b) = stoneBasic a ∩ stoneBasic b) ∧
    stoneBasic (⊥ : L) = ∅ ∧ stoneBasic (⊤ : L) = Set.univ ∧
    (∀ a : L, IsClopen (stoneBasic a)) ∧
    TopologicalSpace.IsTopologicalBasis (Set.range (stoneBasic : L → Set (StoneSpectrum L))) ∧
    TopologicalSpace.IsTopologicalBasis {s : Set (StoneSpectrum L) | IsClopen s} ∧
    T2Space (StoneSpectrum L) ∧ CompletelyRegularSpace (StoneSpectrum L) := by
  classical
  have hmeet (a b : L) : stoneBasic (a ⊓ b) = stoneBasic a ∩ stoneBasic b := by
    ext B
    change (a ⊓ b ∈ B.val) ↔ a ∈ B.val ∧ b ∈ B.val
    have hc := quasipoint_upward_and_meet_closed B.val B.property
    exact ⟨fun h => ⟨hc.1 (a ⊓ b) h a inf_le_left,
      hc.1 (a ⊓ b) h b inf_le_right⟩, fun h => hc.2 a h.1 b h.2⟩
  have hbot : stoneBasic (⊥ : L) = ∅ := by
    ext B
    change (⊥ ∈ B.val) ↔ False
    exact ⟨B.property.1.2.1, False.elim⟩
  have htop : stoneBasic (⊤ : L) = Set.univ := by
    ext B
    change (⊤ ∈ B.val) ↔ True
    constructor
    · intro h; trivial
    · intro h
      obtain ⟨a, ha⟩ := B.property.1.1
      exact (quasipoint_upward_and_meet_closed B.val B.property).1 a ha ⊤ le_top
  have hopen (a : L) : IsOpen (stoneBasic a) :=
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, rfl⟩
  have hclosed (a : L) : IsClosed (stoneBasic a) := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro B hnot
    obtain ⟨b, hb, hba⟩ := quasipoint_nonmember_has_disjoint_member B.val B.property a hnot
    have hsub : stoneBasic b ⊆ (stoneBasic a)ᶜ := by
      intro C hcb hca
      have hz := (quasipoint_upward_and_meet_closed C.val C.property).2 b hcb a hca
      exact C.property.1.2.1 (hba ▸ hz)
    exact Filter.mem_of_superset ((hopen b).mem_nhds hb) hsub
  have hclopen (a : L) : IsClopen (stoneBasic a) := ⟨hclosed a, hopen a⟩
  have hbasis : TopologicalSpace.IsTopologicalBasis (Set.range (stoneBasic : L → Set (StoneSpectrum L))) := by
    have hi : ∀ ⦃s : Set (StoneSpectrum L)⦄, s ∈ Set.range (stoneBasic : L → Set (StoneSpectrum L)) →
        ∀ ⦃t⦄, t ∈ Set.range (stoneBasic : L → Set (StoneSpectrum L)) →
        s ∩ t ∈ Set.range (stoneBasic : L → Set (StoneSpectrum L)) := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ⟨a ⊓ b, hmeet a b⟩
    have hb := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
      (r := Set.range (stoneBasic : L → Set (StoneSpectrum L))) rfl hi
    have hu : Set.univ ∈ Set.range (stoneBasic : L → Set (StoneSpectrum L)) := ⟨⊤, htop⟩
    simpa only [Set.insert_eq_of_mem hu] using hb
  have hclbasis : TopologicalSpace.IsTopologicalBasis {s : Set (StoneSpectrum L) | IsClopen s} := by
    apply TopologicalSpace.IsTopologicalBasis.of_isOpen_of_subset (fun s hs => hs.2) hbasis
    rintro _ ⟨a, rfl⟩
    exact hclopen a
  have ht2 : T2Space (StoneSpectrum L) := by
    constructor
    intro B C hne
    have hnotsub : ¬ B.val ⊆ C.val := by
      intro h
      have heq : C.val = B.val := B.property.2 C.val C.property.1 h
      exact hne (Subtype.ext heq.symm)
    obtain ⟨a, haB, haC⟩ := Set.not_subset.mp hnotsub
    exact ⟨stoneBasic a, (stoneBasic a)ᶜ, hopen a, (hclopen a).compl.isOpen,
      haB, haC, disjoint_compl_right⟩
  refine ⟨hmeet, hbot, htop, hclopen, hbasis, hclbasis, ht2, ?_⟩
  exact CompletelyRegularSpace.of_isTopologicalBasis_clopens hclbasis
