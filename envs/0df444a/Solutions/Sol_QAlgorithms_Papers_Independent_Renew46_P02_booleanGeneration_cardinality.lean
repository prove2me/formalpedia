-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P02.booleanGeneration_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:58:02.315027+00:00
-- url     : https://prove2.me/submissions/69cead79-f9f4-450a-ada3-43f121bc9889

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02
noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

open QAlgorithms.Papers.Independent.Renew46.P02

universe u v

theorem g65c_closure_finite {B : Type u} [BooleanAlgebra B] (G : Set B) (hG : G.Finite) :
    (BooleanSubalgebra.closure G : Set B).Finite := by
  classical
  set s : Set B := latticeClosure (insert ⊥ (insert ⊤ G)) with hs
  have hsf : s.Finite := ((hG.insert ⊤).insert ⊥).latticeClosure
  have hsub : IsSublattice s := isSublattice_latticeClosure
  have hbot : ⊥ ∈ s := subset_latticeClosure (by simp)
  have htop : ⊤ ∈ s := subset_latticeClosure (by simp)
  have hGs : G ⊆ s := fun x hx => subset_latticeClosure (by simp [hx])
  have : Finite s := hsf.to_subtype
  have hfin : (Set.range fun t : Finset (s × s) => t.sup fun x => x.1.1 \ x.2.1).Finite :=
    Set.finite_range _
  refine hfin.subset ?_
  intro a ha
  have ha' : a ∈ BooleanSubalgebra.closure s := BooleanSubalgebra.closure_mono hGs ha
  obtain ⟨t, rfl⟩ := (BooleanSubalgebra.mem_closure_iff_sup_sdiff hsub hbot htop).1 ha'
  exact ⟨t, rfl⟩

theorem g65c_orderClosed_of_finite {B : Type u} [BooleanAlgebra B] (C : BooleanSubalgebra B)
    (hC : (C : Set B).Finite) : IsOrderClosedBoolean C := by
  classical
  intro S hS
  have hSf : S.Finite := hC.subset hS
  refine ⟨hSf.toFinset.sup id, ?_, ?_⟩
  · exact Finset.sup_mem (C : Set B) C.bot_mem (fun _ hx _ hy => C.sup_mem hx hy) hSf.toFinset id
      (fun x hx => hS (by simpa using hx))
  · simpa using (Finset.isLUB_sup_id (s := hSf.toFinset))

theorem g65c_mem_union {B : Type u} [BooleanAlgebra B] (G : Set B) (x : B)
    (hx : x ∈ BooleanSubalgebra.closure G) :
    ∃ F : Finset G, x ∈ BooleanSubalgebra.closure (Subtype.val '' (F : Set G)) := by
  classical
  induction hx using BooleanSubalgebra.closure_bot_sup_induction with
  | mem x hx => exact ⟨{⟨x, hx⟩}, BooleanSubalgebra.subset_closure (by simp)⟩
  | bot => exact ⟨∅, BooleanSubalgebra.bot_mem⟩
  | sup x hx y hy ihx ihy =>
    obtain ⟨F1, h1⟩ := ihx
    obtain ⟨F2, h2⟩ := ihy
    refine ⟨F1 ∪ F2, BooleanSubalgebra.sup_mem ?_ ?_⟩
    · exact BooleanSubalgebra.closure_mono (Set.image_mono (by simp)) h1
    · exact BooleanSubalgebra.closure_mono (Set.image_mono (by simp)) h2
  | compl x hx ih =>
    obtain ⟨F, h⟩ := ih
    exact ⟨F, BooleanSubalgebra.compl_mem h⟩

theorem solution (B : Type u) [BooleanAlgebra B] :
    (∀ G : Set B, G.Finite → CompletelyGenerates G → Finite B) ∧
    (HasAllSuprema B → HasInfiniteMaharamType B →
      ∀ G : Set B, CompletelyGenerates G →
        CompletelyGenerates (BooleanSubalgebra.closure G : Set B) ∧
          Cardinal.mk (BooleanSubalgebra.closure G) = Cardinal.mk G) := by
  refine ⟨fun G hG hgen => ?_, fun _ hM G hgen => ⟨?_, ?_⟩⟩
  · have hfin := g65c_closure_finite G hG
    have htop := hgen _ BooleanSubalgebra.subset_closure (g65c_orderClosed_of_finite _ hfin)
    rw [htop] at hfin
    simp only [BooleanSubalgebra.coe_top] at hfin
    exact Set.finite_univ_iff.1 hfin
  · intro C hC hcl
    exact hgen C (BooleanSubalgebra.subset_closure.trans hC) hcl
  · have hGinf : G.Infinite := fun hf => hM G hf hgen
    have : Infinite G := hGinf.to_subtype
    apply le_antisymm
    · have hsub : (BooleanSubalgebra.closure G : Set B) ⊆
          ⋃ F : Finset G, (BooleanSubalgebra.closure (Subtype.val '' (F : Set G)) : Set B) := by
        intro x hx
        obtain ⟨F, hF⟩ := g65c_mem_union G x hx
        exact Set.mem_iUnion.2 ⟨F, hF⟩
      calc Cardinal.mk (BooleanSubalgebra.closure G)
          ≤ Cardinal.mk (⋃ F : Finset G, (BooleanSubalgebra.closure (Subtype.val '' (F : Set G)) : Set B)) :=
            Cardinal.mk_le_mk_of_subset hsub
        _ ≤ Cardinal.mk (Finset G) * ⨆ F : Finset G,
              Cardinal.mk (BooleanSubalgebra.closure (Subtype.val '' (F : Set G)) : Set B) :=
            Cardinal.mk_iUnion_le _
        _ ≤ Cardinal.mk G * Cardinal.aleph0 := by
            rw [Cardinal.mk_finset_of_infinite]
            gcongr
            refine ciSup_le' fun F => ?_
            have := g65c_closure_finite (Subtype.val '' (F : Set G)) ((F.finite_toSet).image _)
            exact (Cardinal.lt_aleph0_iff_set_finite.2 this).le
        _ = Cardinal.mk G := Cardinal.mul_aleph0_eq (Cardinal.aleph0_le_mk G)
    · exact Cardinal.mk_le_mk_of_subset BooleanSubalgebra.subset_closure
