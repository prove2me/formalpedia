-- Prove2me | solution 1 for StableMSR.Recovery.DecompositionSearch.polynomial_size_table_search
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-14T18:07:06.909672+00:00
-- url     : https://prove2.me/submissions/19436b2b-f032-41b5-bcd4-af66a79795e4

import Definitions.Def_StableMSR_DecompositionSearch_Table
import Theorems.Thm_StableMSR_Recovery_DecompositionSearch_finite_decomposition_search
import Mathlib.Data.Nat.Choose.Bounds
set_option autoImplicit false
open scoped Classical BigOperators
namespace StableMSR.Recovery.Havens
variable {V : Type} [DecidableEq V]
lemma mem_of_walk_closed {G : SimpleGraph V} {C D : Finset V}
    (hclosed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ D → y ∈ C)
    {u v : V} (p : G.Walk u v) (hu : u ∈ C)
    (hp : ∀ z ∈ p.support, z ∈ D) : v ∈ C := by
  induction p with
  | nil => exact hu
  | @cons u v w huv p ih =>
    apply ih (hclosed u hu v huv (hp v (by simp)))
    intro z hz
    exact hp z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hz)

lemma flap_contains_touching {G : SimpleGraph V} {W C D : Finset V}
    (hC : IsFlap G W C) (hD : ConnectedSet G D)
    (havoid : Disjoint W D) (htouch : Touch G C D) : D ⊆ C := by
  obtain ⟨u, huD, huC⟩ : ∃ u, u ∈ D ∧ u ∈ C := by
    rcases htouch with ⟨u, huC, huD⟩ | ⟨x, hx, y, hy, hxy⟩
    · exact ⟨u, huD, huC⟩
    · exact ⟨y, hy, hC.closed x hx y hxy (fun hyW =>
        Finset.disjoint_left.mp havoid hyW hy)⟩
  intro v hv
  obtain ⟨p, hp⟩ := hD.2 u huD v hv
  exact mem_of_walk_closed (fun x hx y hxy hy =>
    hC.closed x hx y hxy (fun hyW => Finset.disjoint_left.mp havoid hyW hy)) p huC hp

noncomputable def componentWithin (G : SimpleGraph V) (U : Finset V) (u : V) : Finset V :=
  by classical exact U.filter (fun v => ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ U)

lemma mem_componentWithin {G : SimpleGraph V} {U : Finset V} {u v : V} :
    v ∈ componentWithin G U u ↔ v ∈ U ∧ ∃ p : G.Walk u v, ∀ z ∈ p.support, z ∈ U := by
  classical
  simp only [componentWithin, Finset.mem_filter]

lemma componentWithin_subset (G : SimpleGraph V) (U : Finset V) (u : V) :
    componentWithin G U u ⊆ U := by
  intro v hv
  exact (mem_componentWithin.mp hv).1

lemma self_mem_componentWithin {G : SimpleGraph V} {U : Finset V} {u : V} (hu : u ∈ U) :
    u ∈ componentWithin G U u := by
  refine mem_componentWithin.mpr ⟨hu, .nil, ?_⟩
  simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using fun z (hz : z = u) => hz ▸ hu

lemma support_subset_componentWithin {G : SimpleGraph V} {U : Finset V}
    {u v : V} (p : G.Walk u v) (hp : ∀ z ∈ p.support, z ∈ U) :
    ∀ z ∈ p.support, z ∈ componentWithin G U u := by
  intro z hz
  refine mem_componentWithin.mpr ⟨hp z hz, p.takeUntil z hz, ?_⟩
  intro w hw
  exact hp w (p.support_takeUntil_subset_support hz hw)

lemma componentWithin_connected {G : SimpleGraph V} {U : Finset V} {u : V} (hu : u ∈ U) :
    ConnectedSet G (componentWithin G U u) := by
  refine ⟨⟨u, self_mem_componentWithin hu⟩, ?_⟩
  intro x hx y hy
  obtain ⟨_, p, hp⟩ := mem_componentWithin.mp hx
  obtain ⟨_, q, hq⟩ := mem_componentWithin.mp hy
  refine ⟨p.reverse.append q, ?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff p.reverse q).mp hz with hz | hz
  · apply support_subset_componentWithin p hp z
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
  · exact support_subset_componentWithin q hq z hz

lemma componentWithin_closed {G : SimpleGraph V} {U : Finset V} {u x y : V}
    (hx : x ∈ componentWithin G U u) (hxy : G.Adj x y) (hy : y ∈ U) :
    y ∈ componentWithin G U u := by
  obtain ⟨_, p, hp⟩ := mem_componentWithin.mp hx
  refine mem_componentWithin.mpr ⟨hy, p.concat hxy, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_concat] at hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hp z hz
  · simpa only [List.mem_singleton] using (show z = y from List.mem_singleton.mp hz) ▸ hy

end StableMSR.Recovery.Havens
namespace StableMSR.Recovery.PartialDecompositions
open Havens
variable {V : Type} [Fintype V] [DecidableEq V]
lemma component_exists (G : SimpleGraph V) (S : Finset V) {v : V} (hv : v ∉ S) :
    ∃ C ∈ components G S, v ∈ C := by
  refine ⟨componentWithin G Sᶜ v, mem_components.mpr ⟨componentWithin_connected (Finset.mem_compl.mpr hv), ?_, ?_⟩,
    self_mem_componentWithin (Finset.mem_compl.mpr hv)⟩
  · exact Finset.disjoint_left.mpr (fun x hx hC =>
      (Finset.mem_compl.mp (componentWithin_subset G Sᶜ v hC)) hx)
  · intro x hx y hxy hy
    exact componentWithin_closed hx hxy (Finset.mem_compl.mpr hy)
lemma components_eq_of_mem {G : SimpleGraph V} {S C D : Finset V}
    (hC : C ∈ components G S) (hD : D ∈ components G S)
    {v : V} (hvC : v ∈ C) (hvD : v ∈ D) : C = D := by
  have c := mem_components.mp hC
  have d := mem_components.mp hD
  exact Finset.Subset.antisymm
    (flap_contains_touching d c.connected c.avoids (.inl ⟨v,hvD,hvC⟩))
    (flap_contains_touching c d.connected d.avoids (.inl ⟨v,hvC,hvD⟩))
end StableMSR.Recovery.PartialDecompositions
open scoped BigOperators
namespace StableMSR.Recovery.DecompositionSearch
open Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]

/- The external vertex boundary, computed in the original graph. -/
lemma boundary_disjoint (G : SimpleGraph V) (C : Finset V) :
    Disjoint (boundary G C) C := by
  exact Finset.disjoint_left.mpr (fun _ hv hc => (mem_boundary.mp hv).1 hc)

lemma boundary_subset {G : SimpleGraph V} {S C : Finset V} (hC : IsFlap G S C) :
    boundary G C ⊆ S := by
  intro v hv
  obtain ⟨hn,u,hu,hadj⟩ := mem_boundary.mp hv
  by_contra hvS
  exact hn (hC.closed u hu v hadj hvS)

/- Replacing a separator by the exact boundary keeps the same component. -/
lemma flap_at_boundary {G : SimpleGraph V} {S C : Finset V} (hC : IsFlap G S C) :
    IsFlap G (boundary G C) C := by
  refine ⟨hC.connected,boundary_disjoint G C,?_⟩
  intro u hu v huv hv
  by_contra hn
  exact hv (mem_boundary.mpr ⟨hn,u,hu,huv⟩)

/- The recursive interiors after choosing a bag B in a current interior C. -/
lemma children_disjoint {G : SimpleGraph V} {B C D E : Finset V}
    (hD : D ∈ children G B C) (hE : E ∈ children G B C) (hne : D ≠ E) :
    Disjoint D E := by
  apply Finset.disjoint_left.mpr
  intro v hvD hvE
  exact hne (components_eq_of_mem (mem_components.mpr (mem_children.mp hD).1)
    (mem_components.mpr (mem_children.mp hE).1) hvD hvE)

theorem children_partition {G : SimpleGraph V} {S C B : Finset V}
    (hC : IsFlap G S C) (hSB : S ⊆ B) :
    (children G B C).biUnion id = C \ B := by
  classical
  ext v
  simp only [Finset.mem_biUnion,id_eq,Finset.mem_sdiff]
  constructor
  · rintro ⟨D,hD,hvD⟩
    obtain ⟨hf,hDC⟩ := mem_children.mp hD
    exact ⟨hDC hvD,fun hvB => Finset.disjoint_left.mp hf.avoids hvB hvD⟩
  · rintro ⟨hvC,hvB⟩
    obtain ⟨D,hD,hvD⟩ := component_exists G B hvB
    have hf := mem_components.mp hD
    have havoid : Disjoint S D := Finset.disjoint_left.mpr
      (fun x hxS hxD => Finset.disjoint_left.mp hf.avoids (hSB hxS) hxD)
    have hDC : D ⊆ C := flap_contains_touching hC hf.connected havoid (.inl ⟨v,hvC,hvD⟩)
    exact ⟨D,mem_children.mpr ⟨hf,hDC⟩,hvD⟩

/- Every chosen vertex is charged once and child interiors partition the remainder. -/
theorem children_card_accounting {G : SimpleGraph V} {S C B : Finset V}
    (hC : IsFlap G S C) (hSB : S ⊆ B) :
    (B ∩ C).card + ∑ D ∈ children G B C, D.card = C.card := by
  classical
  have hs : (∑ D ∈ children G B C, D.card) = (C \ B).card := by
    rw [←Finset.card_biUnion (fun D hD E hE hne => children_disjoint hD hE hne)]
    change ((children G B C).biUnion id).card = (C \ B).card
    rw [children_partition hC hSB]
  rw [hs,Finset.inter_comm]
  exact Finset.card_inter_add_card_sdiff C B

theorem children_strictly_smaller {G : SimpleGraph V} {S C B : Finset V}
    (hC : IsFlap G S C) (hSB : S ⊆ B) (hprogress : (B ∩ C).Nonempty) :
    (∑ D ∈ children G B C, D.card) < C.card ∧
      ∀ D ∈ children G B C, D.card < C.card := by
  have ha := children_card_accounting hC hSB
  have hp := Finset.card_pos.mpr hprogress
  have hs : (∑ D ∈ children G B C, D.card) < C.card := by omega
  refine ⟨hs,?_⟩
  intro D hD
  exact lt_of_le_of_lt (Finset.single_le_sum (fun E _ => Nat.zero_le E.card) hD) hs

end StableMSR.Recovery.DecompositionSearch
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.Havens
open scoped BigOperators Classical
namespace StableMSR.Recovery.DecompositionSearch
open Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]

theorem components_pairwise_disjoint (G : SimpleGraph V) (S : Finset V) :
    (PartialDecompositions.components G S : Set (Finset V)).PairwiseDisjoint id := by
  intro C hC D hD hne
  apply Finset.disjoint_left.mpr
  intro v hvC hvD
  exact hne (components_eq_of_mem hC hD hvC hvD)

theorem components_partition (G : SimpleGraph V) (S : Finset V) :
    (PartialDecompositions.components G S).biUnion id = Finset.univ \ S := by
  classical
  ext v
  simp only [Finset.mem_biUnion,id_eq,Finset.mem_sdiff,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨C,hC,hvC⟩ hvS
    exact Finset.disjoint_left.mp (mem_components.mp hC).avoids hvS hvC
  · intro hvS
    exact component_exists G S hvS

theorem components_card_sum (G : SimpleGraph V) (S : Finset V) :
    (∑ C ∈ PartialDecompositions.components G S, C.card) = Fintype.card V - S.card := by
  classical
  calc
    _ = ((PartialDecompositions.components G S).biUnion id).card := by
      simpa only [id_eq] using (Finset.card_biUnion (components_pairwise_disjoint G S)).symm
    _ = _ := by
      rw [components_partition,Finset.card_sdiff]
      simp

theorem components_subtype_card_sum (G : SimpleGraph V) (S : Finset V) :
    (∑ C : ↥(PartialDecompositions.components G S), C.val.card) = Fintype.card V - S.card := by
  classical
  rw [Finset.sum_coe_sort]
  exact components_card_sum G S

theorem components_empty_card_sum (G : SimpleGraph V) :
    (∑ C : ↥(PartialDecompositions.components G ∅), C.val.card) = Fintype.card V := by
  simpa using components_subtype_card_sum G ∅

end StableMSR.Recovery.DecompositionSearch
namespace StableMSR.Recovery.DecompositionSearch
open Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]
theorem accepts_mono {G : SimpleGraph V} {w m : ℕ} {S C : Finset V}
    (h : accepts G w m S C) : ∀ n, m ≤ n → accepts G w n S C := by
  induction m generalizing S C with
  | zero => exact False.elim h
  | succ m ih =>
    intro n hmn
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨B,hSB,hBC,hBw,hp,hchildren⟩ := h
      refine ⟨B,hSB,hBC,hBw,hp,?_⟩
      intro D hD
      exact ⟨(hchildren D hD).1,ih (hchildren D hD).2 n (by omega)⟩

/- Strict child-size descent removes any need for an unbounded search budget:
an accepted valid component is already accepted within its own cardinality. -/
theorem accepts_normalize {G : SimpleGraph V} {w m : ℕ} {S C : Finset V}
    (hC : IsFlap G S C) (h : accepts G w m S C) :
    accepts G w C.card S C := by
  induction m generalizing S C with
  | zero => exact False.elim h
  | succ m ih =>
    obtain ⟨B,hSB,hBC,hBw,hp,hchildren⟩ := h
    have hcpos := hC.connected.1.card_pos
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcpos)
    rw [hn]
    refine ⟨B,hSB,hBC,hBw,hp,?_⟩
    intro D hD
    have hf : IsFlap G (boundary G D) D := flap_at_boundary (mem_children.mp hD).1
    have hnormalized := ih hf (hchildren D hD).2
    have hsmall := (children_strictly_smaller hC hSB hp).2 D hD
    exact ⟨(hchildren D hD).1,accepts_mono hnormalized n (by omega)⟩

end StableMSR.Recovery.DecompositionSearch
set_option autoImplicit false
open scoped Classical BigOperators
namespace StableMSR.Recovery.DecompositionSearch
open Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]

/- All boundary sets up to the specified cardinality. -/
/- Tight component states indexed by their external boundaries. -/
/- All bags that can introduce vertices in a given state. -/
@[simp] theorem mem_smallSets {w : ℕ} {S : Finset V} :
    S ∈ smallSets w ↔ S.card ≤ w := by
  simp [smallSets]

@[simp] theorem mem_searchStates {G : SimpleGraph V} {w : ℕ} {S C : Finset V} :
    (S,C) ∈ searchStates G w ↔ S.card ≤ w ∧ IsFlap G S C ∧ boundary G C = S := by
  simp only [searchStates,Finset.mem_biUnion,Finset.mem_image,Finset.mem_filter,
    mem_smallSets,mem_components,Prod.mk.injEq]
  constructor
  · rintro ⟨S',hS',C',⟨hf,hb⟩,hS,hC⟩
    rcases hS with rfl
    rcases hC with rfl
    exact ⟨hS',hf,hb⟩
  · rintro ⟨hS,hC,hb⟩
    exact ⟨S,hS,C,⟨hC,hb⟩,rfl,rfl⟩

@[simp] theorem mem_candidateBags {w : ℕ} {S C B : Finset V} :
    B ∈ candidateBags w S C ↔
      S ⊆ B ∧ B ⊆ S ∪ C ∧ B.card ≤ w+1 ∧ (B ∩ C).Nonempty := by
  simp only [candidateBags,Finset.mem_filter,mem_smallSets]
  tauto

/- Enumeration by cardinality avoids scanning all subsets as candidate boundaries. -/
theorem smallSets_eq_biUnion (w : ℕ) :
    (smallSets w : Finset (Finset V)) =
      (Finset.range (w+1)).biUnion (fun i => (Finset.univ : Finset V).powersetCard i) := by
  ext S
  simp only [mem_smallSets,Finset.mem_biUnion,Finset.mem_range,Finset.mem_powersetCard,
    Finset.subset_univ,true_and]
  constructor
  · intro h; exact ⟨S.card,by omega,rfl⟩
  · rintro ⟨i,hi,he⟩; omega

/- A polynomial bound valid also on the empty vertex type. -/
theorem smallSets_card_le (w : ℕ) :
    (smallSets w : Finset (Finset V)).card ≤ (w+1)*(Fintype.card V+1)^w := by
  rw [smallSets_eq_biUnion]
  simpa only [Finset.card_range] using
    Finset.card_biUnion_le_card_mul (Finset.range (w+1))
      (fun i => (Finset.univ : Finset V).powersetCard i) ((Fintype.card V+1)^w) (by
        intro i hi
        rw [Finset.card_powersetCard,Finset.card_univ]
        calc
          (Fintype.card V).choose i ≤ (Fintype.card V)^i := Nat.choose_le_pow _ _
          _ ≤ (Fintype.card V+1)^i := Nat.pow_le_pow_left (by omega) i
          _ ≤ (Fintype.card V+1)^w := Nat.pow_le_pow_right (by omega) (by
            have := Finset.mem_range.mp hi; omega))

/- Nonempty disjoint components are no more numerous than vertices. -/
theorem components_card_le (G : SimpleGraph V) (S : Finset V) :
    (PartialDecompositions.components G S).card ≤ Fintype.card V := by
  calc
    _ = ∑ C ∈ PartialDecompositions.components G S, 1 := by simp
    _ ≤ ∑ C ∈ PartialDecompositions.components G S, C.card :=
      Finset.sum_le_sum (fun C hC => (mem_components.mp hC).connected.1.card_pos)
    _ = Fintype.card V - S.card := components_card_sum G S
    _ ≤ Fintype.card V := Nat.sub_le _ _

/- Only one component index is needed after selecting a boundary. -/
theorem searchStates_card_le (G : SimpleGraph V) (w : ℕ) :
    (searchStates G w).card ≤
      Fintype.card V * (w+1) * (Fintype.card V+1)^w := by
  have hs : (searchStates G w).card ≤ (smallSets w : Finset (Finset V)).card * Fintype.card V := by
    apply Finset.card_biUnion_le_card_mul
    intro S hS
    exact (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans (components_card_le G S))
  exact hs.trans (by
    simpa [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      Nat.mul_le_mul_right (Fintype.card V) (smallSets_card_le (V := V) w))

/- Every state's candidate family obeys the same polynomial bound. -/
theorem candidateBags_card_le (w : ℕ) (S C : Finset V) :
    (candidateBags w S C).card ≤ (w+2)*(Fintype.card V+1)^(w+1) := by
  exact (Finset.card_filter_le _ _).trans (smallSets_card_le (V := V) (w+1))

/- Sum of all candidate counts in one complete pass over the state table. -/
theorem state_candidate_count_le (G : SimpleGraph V) (w : ℕ) :
    (∑ p ∈ searchStates G w, (candidateBags w p.1 p.2).card) ≤
      (Fintype.card V * (w+1) * (Fintype.card V+1)^w) *
        ((w+2)*(Fintype.card V+1)^(w+1)) := by
  calc
    _ ≤ (searchStates G w).card * ((w+2)*(Fintype.card V+1)^(w+1)) := by
      simpa only [smul_eq_mul] using
        Finset.sum_le_card_nsmul (searchStates G w) (fun p => (candidateBags w p.1 p.2).card)
          ((w+2)*(Fintype.card V+1)^(w+1)) (fun p _ => candidateBags_card_le w p.1 p.2)
    _ ≤ _ := Nat.mul_le_mul_right _ (searchStates_card_le G w)

end StableMSR.Recovery.DecompositionSearch

set_option autoImplicit false
open scoped Classical BigOperators
namespace StableMSR.Recovery.DecompositionSearch
open RobertsonSeymour1986.GM5 Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]

/- One synchronous update of the finite state table. Child tests are table
lookups; membership in the fixed state universe enforces tight boundaries. -/
/- Finite tabulation for a specified number of synchronous rounds. -/
lemma child_mem_searchStates {G : SimpleGraph V} {w : ℕ} {B C D : Finset V}
    (hD : D ∈ children G B C) (hw : (boundary G D).card ≤ w) :
    (boundary G D,D) ∈ searchStates G w := by
  exact mem_searchStates.mpr ⟨hw,flap_at_boundary (mem_children.mp hD).1,rfl⟩

/- Table membership is exactly depth-bounded acceptance on the declared
state universe. No accepted state is dropped and no spurious state is added. -/
theorem mem_tabulate_iff (G : SimpleGraph V) (w m : ℕ) (S C : Finset V) :
    (S,C) ∈ tabulate G w m ↔
      (S,C) ∈ searchStates G w ∧ accepts G w m S C := by
  induction m generalizing S C with
  | zero => simp [tabulate,accepts]
  | succ m ih =>
    simp only [tabulate,tableStep,Finset.mem_filter]
    constructor
    · rintro ⟨hs,B,hB,hchildren⟩
      obtain ⟨hSB,hBC,hw,hp⟩ := mem_candidateBags.mp hB
      refine ⟨hs,B,hSB,hBC,hw,hp,?_⟩
      intro D hD
      exact ⟨(hchildren D hD).1,((ih _ _).mp (hchildren D hD).2).2⟩
    · rintro ⟨hs,B,hSB,hBC,hw,hp,hchildren⟩
      refine ⟨hs,B,mem_candidateBags.mpr ⟨hSB,hBC,hw,hp⟩,?_⟩
      intro D hD
      obtain ⟨hwD,haD⟩ := hchildren D hD
      exact ⟨hwD,(ih _ _).mpr ⟨child_mem_searchStates hD hwD,haD⟩⟩

theorem tabulate_mono (G : SimpleGraph V) (w : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    tabulate G w m ⊆ tabulate G w n := by
  rintro ⟨S,C⟩ h
  obtain ⟨hs,ha⟩ := (mem_tabulate_iff G w m S C).mp h
  exact (mem_tabulate_iff G w n S C).mpr ⟨hs,accepts_mono ha n hmn⟩

/- Every valid accepted state has already appeared by round n. -/
theorem tabulate_stabilizes (G : SimpleGraph V) (w m : ℕ)
    (hm : Fintype.card V ≤ m) : tabulate G w m = tabulate G w (Fintype.card V) := by
  apply Finset.Subset.antisymm
  · rintro ⟨S,C⟩ h
    obtain ⟨hs,ha⟩ := (mem_tabulate_iff G w m S C).mp h
    have hf := (mem_searchStates.mp hs).2.1
    exact (mem_tabulate_iff G w (Fintype.card V) S C).mpr
      ⟨hs,accepts_mono (accepts_normalize hf ha) _ (Finset.card_le_univ C)⟩
  · exact tabulate_mono G w hm

lemma initial_mem_searchStates {G : SimpleGraph V} (w : ℕ) {C : Finset V}
    (hC : C ∈ PartialDecompositions.components G ∅) :
    (∅,C) ∈ searchStates G w := by
  have hf := mem_components.mp hC
  have hb : boundary G C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
    (fun v hv => Finset.notMem_empty v (boundary_subset hf hv))
  exact mem_searchStates.mpr ⟨by simp,hf,hb⟩

theorem tableRecognizes_iff (G : SimpleGraph V) (w : ℕ) :
    tableRecognizes G w ↔ recognizes G w := by
  constructor
  · intro h C hC
    exact ((mem_tabulate_iff G w _ ∅ C).mp (h C hC)).2
  · intro h C hC
    exact (mem_tabulate_iff G w _ ∅ C).mpr ⟨initial_mem_searchStates w hC,h C hC⟩

theorem tableRecognizes_iff_treewidthLE (G : SimpleGraph V) (w : ℕ) :
    tableRecognizes G w ↔ TreewidthLE G w :=
  (tableRecognizes_iff G w).trans (finite_decomposition_search G w).1

/- Layer m contains exactly the states with m+1 interior vertices. -/
/- Size-ordered dynamic programming: each transition uses only the completed
smaller layers, and each declared state is considered in exactly one layer. -/
/- The completed size layers contain precisely the accepted states whose
interior fits the current size threshold. -/
theorem mem_sizeTable_iff (G : SimpleGraph V) (w m : ℕ) (S C : Finset V) :
    (S,C) ∈ sizeTable G w m ↔
      (S,C) ∈ searchStates G w ∧ C.card ≤ m ∧ accepts G w C.card S C := by
  induction m generalizing S C with
  | zero =>
    constructor
    · simp [sizeTable]
    · rintro ⟨hs,hcard,_⟩
      have hp := (mem_searchStates.mp hs).2.1.connected.1.card_pos
      omega
  | succ m ih =>
    simp only [sizeTable,Finset.mem_union,Finset.mem_filter,layerStates]
    constructor
    · rintro (hold | ⟨⟨hs,hcard⟩,B,hB,hchildren⟩)
      · obtain ⟨hs,hcm,ha⟩ := (ih S C).mp hold
        exact ⟨hs,by omega,ha⟩
      · obtain ⟨hSB,hBC,hw,hp⟩ := mem_candidateBags.mp hB
        refine ⟨hs,by omega,?_⟩
        rw [hcard]
        refine ⟨B,hSB,hBC,hw,hp,?_⟩
        intro D hD
        obtain ⟨hwD,hdtable⟩ := hchildren D hD
        obtain ⟨_,hDm,haD⟩ := (ih _ _).mp hdtable
        exact ⟨hwD,accepts_mono haD m hDm⟩
    · rintro ⟨hs,hcm,ha⟩
      by_cases hcm' : C.card ≤ m
      · exact Or.inl ((ih S C).mpr ⟨hs,hcm',ha⟩)
      have hcard : C.card = m+1 := by omega
      rw [hcard] at ha
      obtain ⟨B,hSB,hBC,hw,hp,hchildren⟩ := ha
      refine Or.inr ⟨⟨hs,hcard⟩,B,mem_candidateBags.mpr ⟨hSB,hBC,hw,hp⟩,?_⟩
      intro D hD
      obtain ⟨hwD,haD⟩ := hchildren D hD
      have hf := flap_at_boundary (mem_children.mp hD).1
      have hsmall := (children_strictly_smaller (mem_searchStates.mp hs).2.1 hSB hp).2 D hD
      exact ⟨hwD,(ih _ _).mpr
        ⟨child_mem_searchStates hD hwD,by omega,accepts_normalize hf haD⟩⟩

/- The once-per-state, size-ordered table gives the same final result as the
complete n-round depth tabulation. -/
theorem sizeTable_eq_tabulate (G : SimpleGraph V) (w : ℕ) :
    sizeTable G w (Fintype.card V) = tabulate G w (Fintype.card V) := by
  ext p
  obtain ⟨S,C⟩ := p
  rw [mem_sizeTable_iff,mem_tabulate_iff]
  constructor
  · rintro ⟨hs,hcn,ha⟩
    exact ⟨hs,accepts_mono ha _ hcn⟩
  · rintro ⟨hs,ha⟩
    exact ⟨hs,Finset.card_le_univ C,accepts_normalize (mem_searchStates.mp hs).2.1 ha⟩

/- Every additive state charge is counted exactly once across the n layers. -/
theorem sum_layerStates (G : SimpleGraph V) (w : ℕ)
    (f : (Finset V × Finset V) → ℕ) :
    (∑ m ∈ Finset.range (Fintype.card V), ∑ p ∈ layerStates G w m, f p) =
      ∑ p ∈ searchStates G w, f p := by
  classical
  have hpos : ∀ p ∈ searchStates G w, 0 < p.2.card := by
    intro p hp
    exact (mem_searchStates.mp hp).2.1.connected.1.card_pos
  have hmap : ∀ p ∈ searchStates G w, p.2.card - 1 ∈ Finset.range (Fintype.card V) := by
    intro p hp
    have h := hpos p hp
    have hle := Finset.card_le_univ p.2
    rw [Finset.mem_range]
    omega
  calc
    _ = ∑ m ∈ Finset.range (Fintype.card V),
        ∑ p ∈ (searchStates G w).filter (fun p => p.2.card - 1 = m), f p := by
      apply Finset.sum_congr rfl
      intro m hm
      have hsets : layerStates G w m =
          (searchStates G w).filter (fun p => p.2.card - 1 = m) := by
        ext p
        simp only [layerStates,Finset.mem_filter]
        constructor
        · rintro ⟨hp,hcard⟩
          exact ⟨hp,by omega⟩
        · rintro ⟨hp,hcard⟩
          have h := hpos p hp
          exact ⟨hp,by omega⟩
      rw [hsets]
    _ = _ := Finset.sum_fiberwise_of_maps_to hmap f

theorem sizeTableRecognizes_iff_treewidthLE (G : SimpleGraph V) (w : ℕ) :
    sizeTableRecognizes G w ↔ TreewidthLE G w := by
  unfold sizeTableRecognizes
  rw [sizeTable_eq_tabulate]
  exact tableRecognizes_iff_treewidthLE G w

end StableMSR.Recovery.DecompositionSearch


open scoped Classical BigOperators
namespace StableMSR.Recovery.DecompositionSearch
open Havens PartialDecompositions
variable {V : Type} [Fintype V] [DecidableEq V]

/- Number of logical visits when every state is processed once: one state visit,
one eligibility test for every bounded bag, and one table probe per child of an
eligible bag. Finite-family and layer construction/filtering, table operations,
component/boundary construction, indexing, and arithmetic are not counted. -/
lemma children_card_le (G : SimpleGraph V) (B C : Finset V) :
    (children G B C).card ≤ Fintype.card V := by
  apply (Finset.card_le_card (show children G B C ⊆ PartialDecompositions.components G B from ?_)).trans
    (components_card_le G B)
  intro D hD
  exact mem_components.mpr (mem_children.mp hD).1

lemma candidateBags_card_le_smallSets (w : ℕ) (S C : Finset V) :
    (candidateBags w S C).card ≤ (smallSets (V := V) (w+1)).card := by
  exact Finset.card_filter_le _ _

lemma child_probe_count_le (G : SimpleGraph V) (w : ℕ) (S C : Finset V) :
    (∑ B ∈ candidateBags w S C, (children G B C).card) ≤
      (smallSets (V := V) (w+1)).card * Fintype.card V := by
  calc
    _ ≤ ∑ B ∈ candidateBags w S C, Fintype.card V :=
      Finset.sum_le_sum (fun B _ => children_card_le G B C)
    _ = (candidateBags w S C).card * Fintype.card V := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (candidateBags_card_le_smallSets w S C)

/- Polynomial logical enumeration size for the once-per-state table schedule.
This is a count of explicit state/bag/child visits, not an interpreter cost. -/
theorem enumerationVisits_le (G : SimpleGraph V) (w : ℕ) :
    enumerationVisits G w ≤
      (w+1) * (w+2) * (Fintype.card V+1) ^ (2*w+3) := by
  let n := Fintype.card V
  let Q := (w+2) * (n+1) ^ (w+1)
  have hQpos : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (pow_pos (by omega) _))
  have hq : (smallSets (V := V) (w+1)).card ≤ Q := by
    simpa [Q,n,Nat.add_assoc] using smallSets_card_le (V := V) (w+1)
  have hp (p : Finset V × Finset V) :
      1 + (smallSets (V := V) (w+1)).card +
        (∑ B ∈ candidateBags w p.1 p.2, (children G B p.2).card) ≤ (n+2)*Q := by
    have hc := child_probe_count_le G w p.1 p.2
    change _ ≤ (smallSets (V := V) (w+1)).card*n at hc
    have hqn := Nat.mul_le_mul_right n hq
    nlinarith
  have hstates := searchStates_card_le G w
  change (searchStates G w).card ≤ n*(w+1)*(n+1)^w at hstates
  have hnn : n*(n+2) ≤ (n+1)^2 := by nlinarith
  calc
    enumerationVisits G w ≤ ∑ p ∈ searchStates G w, (n+2)*Q :=
      Finset.sum_le_sum (fun p _ => hp p)
    _ = (searchStates G w).card * ((n+2)*Q) := by simp
    _ ≤ (n*(w+1)*(n+1)^w) * ((n+2)*Q) := Nat.mul_le_mul_right _ hstates
    _ = (n*(n+2)) * ((w+1)*(w+2)*(n+1)^w*(n+1)^(w+1)) := by dsimp [Q]; ring
    _ ≤ (n+1)^2 * ((w+1)*(w+2)*(n+1)^w*(n+1)^(w+1)) := Nat.mul_le_mul_right _ hnn
    _ = (w+1)*(w+2)*(n+1)^(2*w+3) := by
      rw [show 2*w+3 = 2+w+(w+1) by omega, pow_add, pow_add]
      ring

/- Size scheduling charges every state and its tests exactly once. -/
theorem layered_enumerationVisits (G : SimpleGraph V) (w : ℕ) :
    (∑ m ∈ Finset.range (Fintype.card V), ∑ p ∈ layerStates G w m,
      (1 + (smallSets (V := V) (w+1)).card +
        ∑ B ∈ candidateBags w p.1 p.2, (children G B p.2).card)) =
      enumerationVisits G w :=
  sum_layerStates G w _

/- Exact size-ordered table semantics and polynomial finite-enumeration bounds.
The visits bound excludes finite-family and layer construction/filtering, table
operations, components/boundaries, indexing, and primitive arithmetic; it is not
an instruction-level runtime theorem. -/
end StableMSR.Recovery.DecompositionSearch

open StableMSR.Recovery.DecompositionSearch
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) :
    (sizeTableRecognizes G w ↔ RobertsonSeymour1986.GM5.TreewidthLE G w) ∧
    (searchStates G w).card ≤
      Fintype.card V * (w+1) * (Fintype.card V+1)^w ∧
    (∑ m ∈ Finset.range (Fintype.card V), ∑ p ∈ layerStates G w m,
      (1 + (smallSets (V := V) (w+1)).card +
        ∑ B ∈ candidateBags w p.1 p.2, (children G B p.2).card)) ≤
      (w+1) * (w+2) * (Fintype.card V+1)^(2*w+3) ∧
    ∀ m (S C : Finset V),
      (S,C) ∈ sizeTable G w m ↔
        (S,C) ∈ searchStates G w ∧ C.card ≤ m ∧ accepts G w C.card S C := by
  refine ⟨sizeTableRecognizes_iff_treewidthLE G w,searchStates_card_le G w,?_,mem_sizeTable_iff G w⟩
  rw [layered_enumerationVisits]
  exact enumerationVisits_le G w

