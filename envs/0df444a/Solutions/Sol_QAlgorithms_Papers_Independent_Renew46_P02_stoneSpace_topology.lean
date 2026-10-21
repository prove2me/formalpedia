-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P02.stoneSpace_topology
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:05:01.558311+00:00
-- url     : https://prove2.me/submissions/eea2a922-d39c-4cc5-b37d-fcc1b5959d0f

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02
noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

open QAlgorithms.Papers.Independent.Renew46.P02

universe u v

theorem g65g_inter {B : Type u} [BooleanAlgebra B] (a b : B) :
    stoneSet (a ⊓ b) = stoneSet a ∩ stoneSet b := by
  ext z; simp [stoneSet]

theorem g65g_compl {B : Type u} [BooleanAlgebra B] (a : B) :
    stoneSet aᶜ = (stoneSet a)ᶜ := by
  ext z; simp only [stoneSet, Set.mem_setOf_eq, Set.mem_compl_iff, map_compl']
  cases z a <;> simp

theorem g65g_sup {B : Type u} [BooleanAlgebra B] (a b : B) :
    stoneSet (a ⊔ b) = stoneSet a ∪ stoneSet b := by
  ext z; simp [stoneSet]

theorem g65g_basis (B : Type u) [BooleanAlgebra B] :
    @TopologicalSpace.IsTopologicalBasis (StonePoint B) (stoneTopology B)
      (Set.range (stoneSet (B := B))) := by
  letI : TopologicalSpace (StonePoint B) := stoneTopology B
  refine ⟨?_, ?_, rfl⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ x hx
    exact ⟨stoneSet (a ⊓ b), ⟨_, rfl⟩, by rw [g65g_inter]; exact hx, by rw [g65g_inter]⟩
  · apply Set.eq_univ_of_forall
    intro z
    exact ⟨stoneSet ⊤, ⟨⊤, rfl⟩, by simp [stoneSet]⟩

theorem g65g_open {B : Type u} [BooleanAlgebra B] (a : B) :
    @IsOpen (StonePoint B) (stoneTopology B) (stoneSet a) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, rfl⟩

theorem g65g_clopen {B : Type u} [BooleanAlgebra B] (a : B) :
    @IsClopen (StonePoint B) (stoneTopology B) (stoneSet a) := by
  letI : TopologicalSpace (StonePoint B) := stoneTopology B
  refine ⟨?_, g65g_open a⟩
  rw [← isOpen_compl_iff, ← g65g_compl]; exact g65g_open _

theorem g65g_compact (B : Type u) [BooleanAlgebra B] :
    @CompactSpace (StonePoint B) (stoneTopology B) := by
  letI : TopologicalSpace (StonePoint B) := stoneTopology B
  let f : StonePoint B → (B → Bool) := fun z => (z : B → Bool)
  have hcont : ∀ a : B, Continuous fun z : StonePoint B => z a := by
    intro a
    rw [continuous_discrete_rng]
    intro b
    cases b
    · have : (fun z : StonePoint B => z a) ⁻¹' {false} = stoneSet aᶜ := by
        rw [g65g_compl]; ext z; simp [stoneSet]
      rw [this]; exact g65g_open _
    · have : (fun z : StonePoint B => z a) ⁻¹' {true} = stoneSet a := by
        ext z; simp [stoneSet]
      rw [this]; exact g65g_open _
  have hind : Topology.IsInducing f := by
    rw [Topology.isInducing_iff]
    apply le_antisymm
    · rw [Pi.topologicalSpace, induced_iInf]
      refine le_iInf fun a => ?_
      rw [induced_compose]
      exact (hcont a).le_induced
    · refine le_generateFrom ?_
      rintro _ ⟨a, rfl⟩
      have : stoneSet a = f ⁻¹' ((fun g : B → Bool => g a) ⁻¹' {true}) := by
        ext z; simp [stoneSet, f]
      rw [this]
      exact isOpen_induced ((isOpen_discrete _).preimage (continuous_apply a))
  have hinj : Function.Injective f := DFunLike.coe_injective
  have hrange : IsClosed (Set.range f) := by
    have : Set.range f =
        (⋂ a : B, ⋂ b : B, {g : B → Bool | g (a ⊔ b) = (g a || g b)}) ∩
        (⋂ a : B, ⋂ b : B, {g : B → Bool | g (a ⊓ b) = (g a && g b)}) ∩
        {g : B → Bool | g ⊤ = true} ∩ {g : B → Bool | g ⊥ = false} := by
      ext g
      constructor
      · rintro ⟨z, rfl⟩
        simp [f]
      · intro hg
        simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hg
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hg
        refine ⟨{ toFun := g, map_sup' := ?_, map_inf' := ?_, map_top' := h3, map_bot' := h4 }, rfl⟩
        · intro a b; rw [h1]; rfl
        · intro a b; rw [h2]; rfl
    rw [this]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      have hc : Continuous fun g : B → Bool => (g a || g b) :=
        (continuous_of_discreteTopology (f := fun p : Bool × Bool => p.1 || p.2)).comp
          (((continuous_apply a).prodMk (continuous_apply b) :
            Continuous fun g : B → Bool => (g a, g b)))
      exact isClosed_eq (continuous_apply _) hc
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      have hc : Continuous fun g : B → Bool => (g a && g b) :=
        (continuous_of_discreteTopology (f := fun p : Bool × Bool => p.1 && p.2)).comp
          (((continuous_apply a).prodMk (continuous_apply b) :
            Continuous fun g : B → Bool => (g a, g b)))
      exact isClosed_eq (continuous_apply _) hc
    · exact isClosed_eq (continuous_apply _) continuous_const
    · exact isClosed_eq (continuous_apply _) continuous_const
  exact Topology.IsClosedEmbedding.compactSpace (f := f) ⟨⟨hind, hinj⟩, hrange⟩

theorem solution (B : Type u) [BooleanAlgebra B] :
    letI : TopologicalSpace (StonePoint B) := stoneTopology B
    CompactSpace (StonePoint B) ∧ T2Space (StonePoint B) ∧
      (∀ G : Set (StonePoint B), IsOpen G ↔
        ∀ z ∈ G, ∃ a : B, z ∈ stoneSet a ∧ stoneSet a ⊆ G) ∧
      TopologicalSpace.IsTopologicalBasis {G : Set (StonePoint B) | IsClopen G} ∧
      {G : Set (StonePoint B) | IsClopen G} = Set.range (stoneSet (B := B)) := by
  letI : TopologicalSpace (StonePoint B) := stoneTopology B
  have hb := g65g_basis B
  haveI := g65g_compact B
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun z w hzw => ?_⟩
    have : ∃ a, z a ≠ w a := by
      by_contra h; push_neg at h; exact hzw (DFunLike.ext _ _ h)
    obtain ⟨a, ha⟩ := this
    cases hz : z a
    · have hw : w a = true := by rw [hz] at ha; cases h : w a <;> simp_all
      refine ⟨stoneSet aᶜ, stoneSet a, g65g_open _, g65g_open _, ?_, hw, ?_⟩
      · rw [g65g_compl]; simp [stoneSet, hz]
      · rw [g65g_compl]; exact disjoint_compl_left
    · have hw : w a = false := by rw [hz] at ha; cases h : w a <;> simp_all
      refine ⟨stoneSet a, stoneSet aᶜ, g65g_open _, g65g_open _, hz, ?_, ?_⟩
      · rw [g65g_compl]; simp [stoneSet, hw]
      · rw [g65g_compl]; exact disjoint_compl_right
  · intro G
    rw [hb.isOpen_iff]
    constructor
    · intro h z hz
      obtain ⟨_, ⟨a, rfl⟩, h1, h2⟩ := h z hz
      exact ⟨a, h1, h2⟩
    · intro h z hz
      obtain ⟨a, h1, h2⟩ := h z hz
      exact ⟨_, ⟨a, rfl⟩, h1, h2⟩
  · refine hb.of_isOpen_of_subset (fun u hu => hu.2) ?_
    rintro _ ⟨a, rfl⟩
    exact g65g_clopen a
  · apply Set.Subset.antisymm
    · intro G hG
      have hGc : IsCompact G := hG.1.isCompact
      obtain ⟨t, ht⟩ := hGc.elim_finite_subcover
        (fun a : {a : B // stoneSet a ⊆ G} => stoneSet a.1) (fun a => g65g_open _)
        (by
          intro z hz
          obtain ⟨_, ⟨a, rfl⟩, h1, h2⟩ := hb.isOpen_iff.1 hG.2 z hz
          exact Set.mem_iUnion.2 ⟨⟨a, h2⟩, h1⟩)
      refine ⟨t.sup (fun a => a.1), ?_⟩
      have key : ∀ s : Finset {a : B // stoneSet a ⊆ G},
          stoneSet (s.sup (fun a => a.1)) = ⋃ i ∈ s, stoneSet i.1 := by
        intro s
        classical
        induction s using Finset.induction_on with
        | empty =>
          rw [Finset.sup_empty]
          ext z
          simp only [stoneSet, Set.mem_iUnion, Set.mem_setOf_eq, map_bot]
          constructor
          · intro h; exact absurd h (by simp)
          · rintro ⟨i, hi, -⟩; exact absurd hi (Finset.notMem_empty _)
        | insert x s hx ih =>
          rw [Finset.sup_insert, g65g_sup, ih, Finset.set_biUnion_insert]
      rw [key]
      apply Set.Subset.antisymm
      · exact Set.iUnion₂_subset fun i _ => i.2
      · exact ht
    · rintro _ ⟨a, rfl⟩
      exact g65g_clopen a
