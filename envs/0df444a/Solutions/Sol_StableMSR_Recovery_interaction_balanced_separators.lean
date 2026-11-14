-- Prove2me | solution 1 for StableMSR.Recovery.interaction_balanced_separators
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T15:17:33.680698+00:00
-- url     : https://prove2.me/submissions/cdc3f07a-04f5-423a-ba07-d58ced0248bd

import Theorems.Thm_StableMSR_Recovery_interaction_subgraph_radius_growth
import Definitions.Def_StableMSR_Recovery_Parameters
import Definitions.Def_TreewidthApprox_Pushed_Setting

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

namespace SeparatorSubmissionAux.Havens
open TreewidthApprox.Pushed
variable {V : Type} [DecidableEq V]

/-- A nonempty vertex set with a path inside it between every two vertices. -/
def ConnectedSet (G : SimpleGraph V) (C : Finset V) : Prop :=
  C.Nonempty ∧ ∀ x ∈ C, ∀ y ∈ C, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ C

/-- Every induced subgraph has a separation of order at most `a`, with each
exclusive side containing at most two thirds of its vertices. -/
def HasBalancedSeparations (G : SimpleGraph V) (a : ℕ) : Prop :=
  ∀ U : Finset V, ∃ L S R : Finset V,
    IsPartition3 U L S R ∧ NoEdge G L R ∧ S.card ≤ a ∧
    3 * L.card ≤ 2 * U.card ∧ 3 * R.card ≤ 2 * U.card


end SeparatorSubmissionAux.Havens


namespace SeparatorSubmissionAux.Havens

open TreewidthApprox.Pushed

variable {V : Type} [DecidableEq V]

/-- The component of `u` in the induced graph on `U`, as an ambient finset.
The intended use assumes `u ∈ U`; otherwise this definition is empty. -/
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

lemma ConnectedSet.induce_connected {G : SimpleGraph V} {C : Finset V}
    (hC : ConnectedSet G C) : (G.induce (C : Set V)).Connected := by
  refine { preconnected := ?_, nonempty := ?_ }
  · intro x y
    obtain ⟨p, hp⟩ := hC.2 x.val x.property y.val y.property
    exact ⟨p.induce (C : Set V) hp⟩
  · obtain ⟨x, hx⟩ := hC.1
    exact ⟨⟨x, hx⟩⟩

lemma componentWithin_induce_connected {G : SimpleGraph V} {U : Finset V} {u : V}
    (hu : u ∈ U) : (G.induce (componentWithin G U u : Set V)).Connected :=
  (componentWithin_connected hu).induce_connected

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

lemma componentWithin_no_edge (G : SimpleGraph V) (U : Finset V) (u : V) :
    NoEdge G (componentWithin G U u) (U \ componentWithin G U u) := by
  intro x hx y hy hxy
  exact (Finset.mem_sdiff.mp hy).2 (componentWithin_closed hx hxy (Finset.mem_sdiff.mp hy).1)

lemma componentWithin_ne_of_not_connected {G : SimpleGraph V} {U : Finset V} {u : V}
    (hu : u ∈ U) (hU : ¬ (G.induce (U : Set V)).Connected) : componentWithin G U u ≠ U := by
  intro heq
  exact hU (heq ▸ componentWithin_induce_connected hu)

/-- Every nonempty disconnected induced subgraph has a nonempty proper
connected component, closed under edges within that induced subgraph. -/
theorem exists_proper_component {G : SimpleGraph V} {U : Finset V}
    (hU : U.Nonempty) (hdisc : ¬ (G.induce (U : Set V)).Connected) :
    ∃ C : Finset V, C.Nonempty ∧ C ⊂ U ∧ (G.induce (C : Set V)).Connected ∧ NoEdge G C (U \ C) := by
  obtain ⟨u, hu⟩ := hU
  refine ⟨componentWithin G U u, ⟨u, self_mem_componentWithin hu⟩, ?_,
    componentWithin_induce_connected hu, componentWithin_no_edge G U u⟩
  exact Finset.ssubset_iff_subset_ne.mpr
    ⟨componentWithin_subset G U u, componentWithin_ne_of_not_connected hu hdisc⟩

end SeparatorSubmissionAux.Havens


set_option autoImplicit false
open scoped Classical
open Finset

namespace SeparatorSubmissionAux.Campbell

/-- A finite ordered set has a median with at least half its elements on either
inclusive side. This is the median of thin BFS layers in Campbell et al., Lemma 6. -/
lemma finset_median (S : Finset ℕ) (hS : S.Nonempty) :
    ∃ j ∈ S, (S.card : ℝ) / 2 ≤ ((S.filter (fun i => i ≤ j)).card : ℝ) ∧
      (S.card : ℝ) / 2 ≤ ((S.filter (fun i => j ≤ i)).card : ℝ) := by
  classical
  have hm : 0 < S.card := Finset.card_pos.mpr hS
  let i : Fin S.card := ⟨S.card / 2, Nat.div_lt_self hm (by omega)⟩
  let e := S.orderEmbOfFin rfl
  have hj : e i ∈ S := S.orderEmbOfFin_mem rfl i
  have hleft : i.val + 1 ≤ (S.filter (fun a => a ≤ e i)).card := by
    have h := Finset.card_le_card_of_injOn e
      (s := Finset.Iic i) (t := S.filter (fun a => a ≤ e i))
      (fun a ha => Finset.mem_filter.mpr ⟨S.orderEmbOfFin_mem rfl a,
        e.monotone (Finset.mem_Iic.mp ha)⟩) e.injective.injOn
    simpa only [Fin.card_Iic] using h
  have hright : S.card - i.val ≤ (S.filter (fun a => e i ≤ a)).card := by
    have h := Finset.card_le_card_of_injOn e
      (s := Finset.Ici i) (t := S.filter (fun a => e i ≤ a))
      (fun a ha => Finset.mem_filter.mpr ⟨S.orderEmbOfFin_mem rfl a,
        e.monotone (Finset.mem_Ici.mp ha)⟩) e.injective.injOn
    simpa only [Fin.card_Ici] using h
  refine ⟨e i, hj, ?_, ?_⟩
  · have hi : i.val = S.card / 2 := rfl
    have hnat : S.card ≤ 2 * (S.filter (fun a => a ≤ e i)).card := by omega
    have hreal : (S.card : ℝ) ≤ 2 * ((S.filter (fun a => a ≤ e i)).card : ℝ) := by exact_mod_cast hnat
    linarith
  · have hi : i.val = S.card / 2 := rfl
    have hnat : S.card ≤ 2 * (S.filter (fun a => e i ≤ a)).card := by omega
    have hreal : (S.card : ℝ) ≤ 2 * ((S.filter (fun a => e i ≤ a)).card : ℝ) := by exact_mod_cast hnat
    linarith

/-- A surjective layering with linear total size has a thin balanced layer.
This isolates the finite counting argument of Campbell et al., Lemma 6 from the
graph metric. The balance concerns the exclusive sides, as used in its proof. -/
theorem thin_layer_separator {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (level : V → ℕ) (p : ℕ) (hp : 0 < p)
    (c : ℝ) (hc : 0 < c)
    (hsurj : ∀ i ≤ p, ∃ v, level v = i)
    (hadj : ∀ a b, G.Adj a b → level b ≤ level a + 1)
    (hsize : (Fintype.card V : ℝ) ≤ c * (p : ℝ)) :
    ∃ L X R : Finset V, TreewidthApprox.Pushed.IsSeparation G L X R ∧
      (X.card : ℝ) < 2 * c ∧
      (L.card : ℝ) ≤ (1 - 1 / (4 * c)) * (Fintype.card V : ℝ) ∧
      (R.card : ℝ) ≤ (1 - 1 / (4 * c)) * (Fintype.card V : ℝ) := by
  classical
  let layer := fun i => Finset.univ.filter (fun v : V => level v = i)
  let I := Finset.Icc 1 p
  let S := I.filter (fun i => (layer i).card < (2 * c : ℝ))
  let T := I.filter (fun i => ¬ (layer i).card < (2 * c : ℝ))
  have hcard : S.card + T.card = p := by
    change (I.filter _).card + (I.filter _).card = p
    rw [Finset.card_filter_add_card_filter_not]
    simp [I]
  have hthick : (T.card : ℝ) * (2 * c) ≤ (Fintype.card V : ℝ) := by
    have hsum : (∑ i ∈ T, (layer i).card) ≤ Fintype.card V := by
      change (∑ i ∈ T, (Finset.univ.filter (fun v : V => level v = i)).card) ≤ _
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)
    calc
      (T.card : ℝ) * (2 * c) = ∑ _i ∈ T, (2 * c) := by simp
      _ ≤ ∑ i ∈ T, ((layer i).card : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact le_of_not_gt (Finset.mem_filter.mp hi).2
      _ ≤ (Fintype.card V : ℝ) := by
        have hsumR : ((∑ i ∈ T, (layer i).card : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hsum
        simpa only [Nat.cast_sum] using hsumR
  have hT : 2 * (T.card : ℝ) ≤ (p : ℝ) := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith
  have hcardR : (S.card : ℝ) + (T.card : ℝ) = (p : ℝ) := by exact_mod_cast hcard
  have hthin : (p : ℝ) / 2 ≤ (S.card : ℝ) := by linarith
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have hz : S.card = 0 := by omega
    have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    rw [hz, Nat.cast_zero] at hthin
    linarith
  obtain ⟨j, hj, hjleft, hjright⟩ := finset_median S hS
  have hjthin : ((layer j).card : ℝ) < 2 * c := (Finset.mem_filter.mp hj).2
  have hleftcount : (S.filter (fun i => i ≤ j)).card ≤
      (Finset.univ.filter (fun v : V => level v ≤ j)).card := by
    apply Finset.card_le_card_of_surjOn level
    intro i hi
    obtain ⟨hiS, hij⟩ := Finset.mem_filter.mp hi
    have hip : i ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hiS).1).2
    obtain ⟨v, hv⟩ := hsurj i hip
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hv] using hij⟩, hv⟩
  have hrightcount : (S.filter (fun i => j ≤ i)).card ≤
      (Finset.univ.filter (fun v : V => j ≤ level v)).card := by
    apply Finset.card_le_card_of_surjOn level
    intro i hi
    obtain ⟨hiS, hji⟩ := Finset.mem_filter.mp hi
    have hip : i ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hiS).1).2
    obtain ⟨v, hv⟩ := hsurj i hip
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hv] using hji⟩, hv⟩
  have hleftR : ((S.filter (fun i => i ≤ j)).card : ℝ) ≤
      ((Finset.univ.filter (fun v : V => level v ≤ j)).card : ℝ) := by exact_mod_cast hleftcount
  have hrightR : ((S.filter (fun i => j ≤ i)).card : ℝ) ≤
      ((Finset.univ.filter (fun v : V => j ≤ level v)).card : ℝ) := by exact_mod_cast hrightcount
  have hquarter : (Fintype.card V : ℝ) / (4 * c) ≤ (p : ℝ) / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * c)).2
    nlinarith
  have hleft : (Fintype.card V : ℝ) / (4 * c) ≤
      ((Finset.univ.filter (fun v : V => level v ≤ j)).card : ℝ) := by linarith
  have hright : (Fintype.card V : ℝ) / (4 * c) ≤
      ((Finset.univ.filter (fun v : V => j ≤ level v)).card : ℝ) := by linarith
  let L := Finset.univ.filter (fun v : V => level v < j)
  let X := layer j
  let R := Finset.univ.filter (fun v : V => j < level v)
  have hpart : TreewidthApprox.Pushed.IsPartition3 Finset.univ L X R := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro v hvL hvX
      have h1 := (Finset.mem_filter.mp hvL).2
      have h2 := (Finset.mem_filter.mp hvX).2
      omega
    · apply Finset.disjoint_left.mpr
      intro v hvL hvR
      have h1 := (Finset.mem_filter.mp hvL).2
      have h2 := (Finset.mem_filter.mp hvR).2
      omega
    · apply Finset.disjoint_left.mpr
      intro v hvX hvR
      have h1 := (Finset.mem_filter.mp hvX).2
      have h2 := (Finset.mem_filter.mp hvR).2
      omega
    · ext v
      rcases lt_trichotomy (level v) j with h | h | h <;> simp [L, X, R, layer, h]
  have hno : TreewidthApprox.Pushed.NoEdge G L R := by
    intro a ha b hb hab
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    have h3 := hadj a b hab
    omega
  have hLcard : (L.card : ℝ) + ((Finset.univ.filter (fun v : V => j ≤ level v)).card : ℝ) =
      (Fintype.card V : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (p := fun v => level v < j)
    simp only [not_lt, Finset.card_univ] at h
    exact_mod_cast h
  have hRcard : (R.card : ℝ) + ((Finset.univ.filter (fun v : V => level v ≤ j)).card : ℝ) =
      (Fintype.card V : ℝ) := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (p := fun v => j < level v)
    simp only [not_lt, Finset.card_univ] at h
    exact_mod_cast h
  have hid : (1 - 1 / (4 * c)) * (Fintype.card V : ℝ) =
      (Fintype.card V : ℝ) - (Fintype.card V : ℝ) / (4 * c) := by ring
  refine ⟨L, X, R, ⟨hpart, hno⟩, hjthin, ?_, ?_⟩ <;> rw [hid] <;> linarith

/-- Every distance level on a shortest path to a farthest point is occupied. -/
lemma distance_level_surjective {V : Type} (G : SimpleGraph V) (hG : G.Connected)
    (v z : V) (i : ℕ) (hi : i ≤ G.dist v z) : ∃ y, G.dist v y = i := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v z
  refine ⟨p.getVert i, ?_⟩
  have ht := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_take i)
  rw [SimpleGraph.Walk.take_length, min_eq_left (by omega : i ≤ p.length)] at ht
  exact ht.symm

/-- Campbell et al., Lemma 6 for a connected graph, including the singleton case.
The hypothesis is the actual graph-radius growth condition, not a separator assumption. -/
theorem connected_growth_separator {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (c : ℝ) (hc : 1 ≤ c)
    (hgrowth : ∀ r : ℕ, 1 ≤ r → (∃ v, ∀ y, G.dist v y ≤ r) →
      (Fintype.card V : ℝ) ≤ c * (r : ℝ)) :
    ∃ L X R : Finset V, TreewidthApprox.Pushed.IsSeparation G L X R ∧
      (X.card : ℝ) < 2 * c ∧
      (L.card : ℝ) ≤ (1 - 1 / (4 * c)) * (Fintype.card V : ℝ) ∧
      (R.card : ℝ) ≤ (1 - 1 / (4 * c)) * (Fintype.card V : ℝ) := by
  classical
  letI : Nonempty V := hG.nonempty
  let v : V := Classical.choice hG.nonempty
  obtain ⟨z, _, hz⟩ := Finset.exists_max_image (Finset.univ : Finset V) (G.dist v) Finset.univ_nonempty
  have hmax : ∀ y, G.dist v y ≤ G.dist v z := fun y => hz y (Finset.mem_univ _)
  have hc0 : 0 < c := by linarith
  by_cases hp : G.dist v z = 0
  · have hone : (Finset.univ : Finset V) = {v} := by
      ext y
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact ((hG.dist_eq_zero_iff).mp (Nat.eq_zero_of_le_zero (by simpa [hp] using hmax y))).symm
    have hcard : Fintype.card V = 1 := by
      rw [← Finset.card_univ, hone, Finset.card_singleton]
    have hα : 0 ≤ 1 - 1 / (4 * c) := by
      apply sub_nonneg.mpr
      apply (div_le_one (by positivity : 0 < 4 * c)).2
      linarith
    refine ⟨∅, Finset.univ, ∅, ?_, ?_, ?_, ?_⟩
    · simp [TreewidthApprox.Pushed.IsSeparation, TreewidthApprox.Pushed.IsPartition3,
        TreewidthApprox.Pushed.NoEdge]
    · simp only [Finset.card_univ, hcard, Nat.cast_one]
      linarith
    · simp only [Finset.card_empty, Nat.cast_zero, hcard, Nat.cast_one, mul_one]
      exact hα
    · simp only [Finset.card_empty, Nat.cast_zero, hcard, Nat.cast_one, mul_one]
      exact hα
  · have hp0 : 0 < G.dist v z := Nat.pos_of_ne_zero hp
    apply thin_layer_separator G (G.dist v) (G.dist v z) hp0 c hc0
      (fun i hi => distance_level_surjective G hG v z i hi)
    · intro a b hab
      rcases hab.diff_dist_adj (u := v) with h | h | h <;> omega
    · exact hgrowth (G.dist v z) (by omega) ⟨v, hmax⟩

end SeparatorSubmissionAux.Campbell


set_option autoImplicit false
open scoped Classical
open TreewidthApprox.Pushed

namespace SeparatorSubmissionAux.Campbell

lemma partition_subsets {V : Type} [Fintype V] [DecidableEq V]
    {W L X R : Finset V} (h : IsPartition3 W L X R) : L ⊆ W ∧ X ⊆ W ∧ R ⊆ W := by
  rw [← h.2.2.2]
  exact ⟨Finset.subset_union_left.trans Finset.subset_union_left,
    Finset.subset_union_right.trans Finset.subset_union_left, Finset.subset_union_right⟩

lemma partition_card {V : Type} [Fintype V] [DecidableEq V]
    {W L X R : Finset V} (h : IsPartition3 W L X R) : W.card = L.card + X.card + R.card := by
  rw [← h.2.2.2, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h.2.1, h.2.2.1⟩),
    Finset.card_union_of_disjoint h.1]

lemma partition_swap {V : Type} [Fintype V] [DecidableEq V]
    {W L X R : Finset V} (h : IsPartition3 W L X R) : IsPartition3 W R X L := by
  refine ⟨h.2.2.1.symm, h.2.1.symm, h.1.symm, ?_⟩
  simpa [Finset.union_comm, Finset.union_left_comm, Finset.union_assoc] using h.2.2.2

lemma noEdge_swap {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {L R : Finset V} (h : NoEdge G L R) : NoEdge G R L := by
  intro r hr l hl hrl
  exact h l hl r hr hrl.symm

/-- Refine the right exclusive side by another separation, charging only its new separator. -/
lemma refine_separation {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {W L X R A Y B : Finset V}
    (hpart : IsPartition3 W L X R) (hno : NoEdge G L R)
    (hsubpart : IsPartition3 R A Y B) (hsubno : NoEdge G A B) :
    IsPartition3 W (L ∪ A) (X ∪ Y) B ∧ NoEdge G (L ∪ A) B ∧
      (L ∪ A).card = L.card + A.card ∧ (X ∪ Y).card = X.card + Y.card := by
  obtain ⟨hAR, hYR, hBR⟩ := partition_subsets hsubpart
  have hLA : Disjoint L A := hpart.2.1.mono_right hAR
  have hLY : Disjoint L Y := hpart.2.1.mono_right hYR
  have hLB : Disjoint L B := hpart.2.1.mono_right hBR
  have hXA : Disjoint X A := hpart.2.2.1.mono_right hAR
  have hXY : Disjoint X Y := hpart.2.2.1.mono_right hYR
  have hXB : Disjoint X B := hpart.2.2.1.mono_right hBR
  have hnew : IsPartition3 W (L ∪ A) (X ∪ Y) B := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_right.mpr ⟨hpart.1, hLY⟩,
          Finset.disjoint_union_right.mpr ⟨hXA.symm, hsubpart.1⟩⟩
    · exact Finset.disjoint_union_left.mpr ⟨hLB, hsubpart.2.1⟩
    · exact Finset.disjoint_union_left.mpr ⟨hXB, hsubpart.2.2.1⟩
    · calc
        (L ∪ A) ∪ (X ∪ Y) ∪ B = L ∪ X ∪ (A ∪ Y ∪ B) := by
          ac_rfl
        _ = W := by rw [hsubpart.2.2.2, hpart.2.2.2]
  refine ⟨hnew, ?_, Finset.card_union_of_disjoint hLA, Finset.card_union_of_disjoint hXY⟩
  intro a ha b hb hab
  rcases Finset.mem_union.mp ha with ha | ha
  · exact hno a ha b (hBR hb) hab
  · exact hsubno a ha b hb hab

/-- A separation of a region can be oriented so its right inclusive side contains
at least half of that region. -/
lemma orient_separation {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α : ℝ) (s : ℕ)
    (h : ∃ L X R : Finset V, IsPartition3 W L X R ∧ NoEdge G L R ∧ X.card ≤ s ∧
      (L.card : ℝ) ≤ α * W.card ∧ (R.card : ℝ) ≤ α * W.card) :
    ∃ L X R : Finset V, IsPartition3 W L X R ∧ NoEdge G L R ∧ X.card ≤ s ∧
      (L.card : ℝ) ≤ α * W.card ∧ (R.card : ℝ) ≤ α * W.card ∧
      W.card ≤ 2 * (X.card + R.card) := by
  obtain ⟨L, X, R, hp, hn, hs, hl, hr⟩ := h
  have hcard := partition_card hp
  by_cases hle : L.card ≤ R.card
  · exact ⟨L, X, R, hp, hn, hs, hl, hr, by omega⟩
  · exact ⟨R, X, L, partition_swap hp, noEdge_swap hn, hs, hr, hl, by omega⟩

/-- One refinement of an overlarge right side makes the other side 2/3-balanced,
multiplies the right-side bound by α, and adds at most s separator vertices. -/
lemma refine_heavy_right {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {W L X R : Finset V} (α β : ℝ) (hα : 0 ≤ α)
    (s q : ℕ) (hp : IsPartition3 W L X R) (hn : NoEdge G L R) (hX : X.card ≤ q)
    (hheavy : (2 / 3 : ℝ) * W.card < (R.card : ℝ))
    (hR : (R.card : ℝ) ≤ β * W.card)
    (hsep : ∃ A Y B : Finset V, IsPartition3 R A Y B ∧ NoEdge G A B ∧ Y.card ≤ s ∧
      (A.card : ℝ) ≤ α * R.card ∧ (B.card : ℝ) ≤ α * R.card) :
    ∃ L' X' R' : Finset V, IsPartition3 W L' X' R' ∧ NoEdge G L' R' ∧ X'.card ≤ q + s ∧
      (L'.card : ℝ) ≤ (2 / 3 : ℝ) * W.card ∧ (R'.card : ℝ) ≤ (α * β) * W.card := by
  obtain ⟨A, Y, B, hsp, hsn, hY, _, hB, horient⟩ := orient_separation G R α s hsep
  obtain ⟨hpart, hno, hLA, hXY⟩ := refine_separation G hp hn hsp hsn
  have htotal := partition_card hp
  have hlocal := partition_card hsp
  have htotalR : (W.card : ℝ) = (L.card : ℝ) + (X.card : ℝ) + (R.card : ℝ) := by exact_mod_cast htotal
  have hlocalR : (R.card : ℝ) = (A.card : ℝ) + (Y.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hlocal
  have horientR : (R.card : ℝ) ≤ 2 * ((Y.card : ℝ) + (B.card : ℝ)) := by exact_mod_cast horient
  refine ⟨L ∪ A, X ∪ Y, B, hpart, hno, ?_, ?_, ?_⟩
  · rw [hXY]; omega
  · rw [hLA, Nat.cast_add]
    have hX0 : (0 : ℝ) ≤ (X.card : ℝ) := by positivity
    linarith
  · have hmul := mul_le_mul_of_nonneg_left hR hα
    nlinarith

/-- Iterated balancing (Campbell et al., Lemma 4), before selecting the logarithmic
iteration count. The separator grows linearly in the number of refinements. -/
theorem balance_iterations {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α : ℝ) (hα : 0 ≤ α) (s : ℕ)
    (hsep : ∀ U ⊆ W, ∃ L X R : Finset V, IsPartition3 U L X R ∧ NoEdge G L R ∧ X.card ≤ s ∧
      (L.card : ℝ) ≤ α * U.card ∧ (R.card : ℝ) ≤ α * U.card) (m : ℕ) :
    ∃ L X R : Finset V, IsPartition3 W L X R ∧ NoEdge G L R ∧ X.card ≤ m * s ∧
      (L.card : ℝ) ≤ max (2 / 3 : ℝ) (α ^ m) * W.card ∧
      (R.card : ℝ) ≤ max (2 / 3 : ℝ) (α ^ m) * W.card := by
  induction m with
  | zero =>
      refine ⟨W, ∅, ∅, ?_, ?_, by simp, ?_, ?_⟩
      · simp [IsPartition3]
      · simp [NoEdge]
      · norm_num
      · norm_num
  | succ m ih =>
      obtain ⟨L, X, R, hp, hn, hX, hL, hR⟩ := ih
      have hW0 : (0 : ℝ) ≤ (W.card : ℝ) := by positivity
      have hbudget : m * s ≤ (m + 1) * s := Nat.mul_le_mul_right s (Nat.le_succ m)
      have hfloor : (2 / 3 : ℝ) * W.card ≤ max (2 / 3 : ℝ) (α ^ (m+1)) * W.card :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hW0
      have hpower : α ^ (m+1) * W.card ≤ max (2 / 3 : ℝ) (α ^ (m+1)) * W.card :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hW0
      by_cases hl : (L.card : ℝ) ≤ (2 / 3 : ℝ) * W.card
      · by_cases hr : (R.card : ℝ) ≤ (2 / 3 : ℝ) * W.card
        · exact ⟨L, X, R, hp, hn, hX.trans hbudget, hl.trans hfloor, hr.trans hfloor⟩
        · have hheavy : (2 / 3 : ℝ) * W.card < (R.card : ℝ) := lt_of_not_ge hr
          have hbound : (R.card : ℝ) ≤ α ^ m * W.card := by
            by_cases hm : (2 / 3 : ℝ) ≤ α ^ m
            · simpa only [max_eq_right hm] using hR
            · have hh : (R.card : ℝ) ≤ (2 / 3 : ℝ) * W.card := by
                simpa only [max_eq_left (le_of_not_ge hm)] using hR
              exact False.elim (not_lt_of_ge hh hheavy)
          obtain ⟨A, Y, B, hpart, hno, hY, hA, hB⟩ := refine_heavy_right G α (α^m) hα s (m*s)
            hp hn hX hheavy hbound (hsep R (partition_subsets hp).2.2)
          refine ⟨A, Y, B, hpart, hno, ?_, hA.trans hfloor, ?_⟩
          · simpa only [Nat.add_mul, Nat.one_mul] using hY
          · apply le_trans ?_ hpower
            simpa only [pow_succ', mul_assoc] using hB
      · have hheavy : (2 / 3 : ℝ) * W.card < (L.card : ℝ) := lt_of_not_ge hl
        have hbound : (L.card : ℝ) ≤ α ^ m * W.card := by
          by_cases hm : (2 / 3 : ℝ) ≤ α ^ m
          · simpa only [max_eq_right hm] using hL
          · have hh : (L.card : ℝ) ≤ (2 / 3 : ℝ) * W.card := by
              simpa only [max_eq_left (le_of_not_ge hm)] using hL
            exact False.elim (not_lt_of_ge hh hheavy)
        obtain ⟨A, Y, B, hpart, hno, hY, hA, hB⟩ := refine_heavy_right G α (α^m) hα s (m*s)
          (partition_swap hp) (noEdge_swap hn) hX hheavy hbound (hsep L (partition_subsets hp).1)
        refine ⟨A, Y, B, hpart, hno, ?_, hA.trans hfloor, ?_⟩
        · simpa only [Nat.add_mul, Nat.one_mul] using hY
        · apply le_trans ?_ hpower
          simpa only [pow_succ', mul_assoc] using hB

/-- Split a disconnected induced graph into two nonempty edge-separated sides,
oriented with the smaller side first. -/
lemma disconnected_split {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (hU : U.Nonempty)
    (hdisc : ¬ (G.induce (U : Set V)).Connected) :
    ∃ L R : Finset V, IsPartition3 U L ∅ R ∧ NoEdge G L R ∧
      L.card ≤ R.card ∧ L ⊂ U ∧ R ⊂ U := by
  classical
  obtain ⟨C, hCn, hCU, _, hno⟩ := SeparatorSubmissionAux.Havens.exists_proper_component hU hdisc
  have hCsub : C ⊆ U := Finset.Subset.refl C |>.trans (Finset.ssubset_iff_subset_ne.mp hCU).1
  let D := U \ C
  have hdis : Disjoint C D := disjoint_sdiff_self_right
  have hcov : C ∪ D = U := Finset.union_sdiff_of_subset hCsub
  have hcard : C.card + D.card = U.card := by rw [← Finset.card_union_of_disjoint hdis, hcov]
  have hCpos : 0 < C.card := Finset.card_pos.mpr hCn
  have hDlt : D.card < U.card := by omega
  have hDsub : D ⊆ U := Finset.sdiff_subset
  have hDU : D ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hDsub, by intro heq; rw [heq] at hDlt; omega⟩
  have hp : IsPartition3 U C ∅ D := by
    exact ⟨Finset.disjoint_empty_right _, hdis, Finset.disjoint_empty_left _, by simpa using hcov⟩
  by_cases hle : C.card ≤ D.card
  · exact ⟨C, D, hp, hno, hle, hCU, hDU⟩
  · exact ⟨D, C, partition_swap hp, noEdge_swap hno, by omega, hDU, hCU⟩

/-- Campbell et al., Lemma 5: connected induced subgraphs suffice for balanced
separations of every induced subgraph. No component is treated as an oracle. -/
theorem separators_from_connected {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α : ℝ) (hα : (2 / 3 : ℝ) ≤ α) (s : ℕ)
    (hconnected : ∀ U ⊆ W, (G.induce (U : Set V)).Connected →
      ∃ L X R : Finset V, IsPartition3 U L X R ∧ NoEdge G L R ∧ X.card ≤ s ∧
        (L.card : ℝ) ≤ α * U.card ∧ (R.card : ℝ) ≤ α * U.card) :
    ∀ U ⊆ W, ∃ L X R : Finset V, IsPartition3 U L X R ∧ NoEdge G L R ∧ X.card ≤ s ∧
      (L.card : ℝ) ≤ α * U.card ∧ (R.card : ℝ) ≤ α * U.card := by
  classical
  have hα0 : 0 ≤ α := by linarith
  intro U
  refine Finset.strongInductionOn U ?_
  intro U ih hUW
  by_cases hU : U.Nonempty
  swap
  · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    exact ⟨∅, ∅, ∅, by simp [IsPartition3], by simp [NoEdge], by simp, by simp, by simp⟩
  by_cases hconn : (G.induce (U : Set V)).Connected
  · exact hconnected U hUW hconn
  obtain ⟨L, R, hp, hn, hLR, _, hRU⟩ := disconnected_split G U hU hconn
  have hRsub := (partition_subsets hp).2.2
  have hU0 : (0 : ℝ) ≤ (U.card : ℝ) := by positivity
  have hαbound : (2 / 3 : ℝ) * U.card ≤ α * U.card := mul_le_mul_of_nonneg_right hα hU0
  by_cases hsmall : (R.card : ℝ) ≤ (2 / 3 : ℝ) * U.card
  · have hLRreal : (L.card : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast hLR
    exact ⟨L, ∅, R, hp, hn, by simp, hLRreal.trans (hsmall.trans hαbound), hsmall.trans hαbound⟩
  · have hheavy : (2 / 3 : ℝ) * U.card < (R.card : ℝ) := lt_of_not_ge hsmall
    have hRbound : (R.card : ℝ) ≤ 1 * U.card := by
      simpa only [one_mul] using (show (R.card : ℝ) ≤ (U.card : ℝ) by exact_mod_cast Finset.card_le_card hRsub)
    obtain ⟨A, X, B, hpart, hno, hX, hA, hB⟩ := refine_heavy_right G α 1 hα0 s 0 hp hn
      (by simp) hheavy hRbound (ih R hRU (hRsub.trans hUW))
    exact ⟨A, X, B, hpart, hno, by simpa using hX, hA.trans hαbound, by simpa using hB⟩
end SeparatorSubmissionAux.Campbell


set_option autoImplicit false
open scoped Classical
open TreewidthApprox.Pushed

namespace SeparatorSubmissionAux.Campbell

/-- Radius is measured in each connected induced subgraph, including all its
vertices; the ambient finite graph need not be connected. -/
def HereditaryRadiusGrowth {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : ℝ) : Prop :=
  ∀ U : Finset V, (G.induce (U : Set V)).Connected →
    ∀ r : ℕ, 1 ≤ r → (∃ x : U, ∀ y : U, (G.induce (U : Set V)).dist x y ≤ r) →
      (U.card : ℝ) ≤ c * (r : ℝ)

/-- Forget subtype coordinates in a separation of an induced graph. -/
lemma lift_induced_separation {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (L X R : Finset U)
    (hsep : IsSeparation (G.induce (U : Set V)) L X R) :
    IsPartition3 U (L.image Subtype.val) (X.image Subtype.val) (R.image Subtype.val) ∧
      NoEdge G (L.image Subtype.val) (R.image Subtype.val) ∧
      (L.image Subtype.val).card = L.card ∧ (X.image Subtype.val).card = X.card ∧
      (R.image Subtype.val).card = R.card := by
  classical
  have hinj : Function.Injective (Subtype.val : U → V) := Subtype.val_injective
  have himage : (Finset.univ : Finset U).image Subtype.val = U := by
    ext v
    simp
  have hp := hsep.1
  refine ⟨?_, ?_, Finset.card_image_of_injective _ hinj,
    Finset.card_image_of_injective _ hinj, Finset.card_image_of_injective _ hinj⟩
  · refine ⟨(Finset.disjoint_image hinj).mpr hp.1,
      (Finset.disjoint_image hinj).mpr hp.2.1, (Finset.disjoint_image hinj).mpr hp.2.2.1, ?_⟩
    rw [← Finset.image_union, ← Finset.image_union, hp.2.2.2, himage]
  · intro a ha b hb hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact hsep.2 a' ha' b' hb' hab

/-- A small explicit logarithm estimate, proved from the first four exponential terms. -/
lemma log_three_halves_le : Real.log (3 / 2 : ℝ) ≤ 49 / 120 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3 / 2)).2
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 49 / 120) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- The logarithmic number of balancing rounds has the bound giving exactly
the coefficient 49 in Campbell's final estimate. -/
lemma balancing_rounds (c : ℝ) (hc : 1 ≤ c) :
    ∃ m : ℕ, (1 - 1 / (4 * c)) ^ m ≤ (2 / 3 : ℝ) ∧
      (m : ℝ) ≤ (49 / 30 : ℝ) * c + 1 := by
  have hc0 : 0 < c := by linarith
  let α := 1 - 1 / (4 * c)
  have hα0 : 0 < α := by
    dsimp [α]
    have hdiv : 1 / (4 * c) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    linarith
  have hα1 : α < 1 := by
    dsimp [α]
    have hdiv : 0 < 1 / (4 * c) := by positivity
    linarith
  let t := Real.logb α (2 / 3)
  have ht0 : 0 ≤ t := Real.logb_nonneg_of_base_lt_one hα0 hα1 (by norm_num) (by norm_num)
  have hlog : Real.log α ≤ -1 / (4 * c) := by
    calc
      Real.log α ≤ α - 1 := Real.log_le_sub_one_of_pos hα0
      _ = -1 / (4 * c) := by dsimp [α]; ring
  have hlogneg : Real.log α < 0 := Real.log_neg hα0 hα1
  have hlogfrac : Real.log (2 / 3 : ℝ) = - Real.log (3 / 2 : ℝ) := by
    have heq : (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ := by norm_num
    rw [heq, Real.log_inv]
  have ht : t ≤ (49 / 30 : ℝ) * c := by
    change Real.log (2 / 3 : ℝ) / Real.log α ≤ _
    apply (div_le_iff_of_neg hlogneg).2
    rw [hlogfrac]
    have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (49 / 30 : ℝ) * c by positivity)
    have heq : ((49 / 30 : ℝ) * c) * (-1 / (4 * c)) = -49 / 120 := by
      field_simp
      <;> ring
    rw [heq] at hmul
    linarith [log_three_halves_le]
  refine ⟨⌈t⌉₊, ?_, ?_⟩
  · have hp := (Real.logb_le_iff_le_rpow_of_base_lt_one hα0 hα1
      (by norm_num : (0 : ℝ) < 2 / 3)).mp (Nat.le_ceil t)
    simpa only [Real.rpow_natCast] using hp
  · exact (Nat.ceil_lt_add_one ht0).le.trans (by linarith)

/-- The full separator consequence of Campbell's linear-growth argument.
The remaining treewidth implication is precisely Dvořák–Norin's theorem. -/
theorem hereditary_growth_balanced_separators {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : ℝ) (hc : 1 ≤ c) (hgrowth : HereditaryRadiusGrowth G c) :
    ∃ a : ℕ, (15 * a : ℝ) ≤ 49 * c ^ 2 + 30 * c ∧
      SeparatorSubmissionAux.Havens.HasBalancedSeparations G a := by
  classical
  let α := 1 - 1 / (4 * c)
  let s := ⌊2 * c⌋₊
  have hc0 : 0 < c := by linarith
  have hα : (2 / 3 : ℝ) ≤ α := by
    have hdiv : 1 / (4 * c) ≤ (1 / 4 : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * c) (by norm_num : (0 : ℝ) < 4)).2
      linarith
    dsimp [α]
    linarith
  have hα0 : 0 ≤ α := by linarith
  have hconnected : ∀ U ⊆ (Finset.univ : Finset V), (G.induce (U : Set V)).Connected →
      ∃ L X R : Finset V, IsPartition3 U L X R ∧ NoEdge G L R ∧ X.card ≤ s ∧
        (L.card : ℝ) ≤ α * U.card ∧ (R.card : ℝ) ≤ α * U.card := by
    intro U _ hU
    have hg : ∀ r : ℕ, 1 ≤ r → (∃ v : U, ∀ y : U, (G.induce (U : Set V)).dist v y ≤ r) →
        (Fintype.card U : ℝ) ≤ c * (r : ℝ) := by
      intro r hr hv
      simpa only [Fintype.card_coe] using hgrowth U hU r hr hv
    obtain ⟨L, X, R, hp, hX, hL, hR⟩ := connected_growth_separator (G.induce (U : Set V)) hU c hc hg
    obtain ⟨hpart, hno, hLc, hXc, hRc⟩ := lift_induced_separation G U L X R hp
    refine ⟨L.image Subtype.val, X.image Subtype.val, R.image Subtype.val, hpart, hno, ?_, ?_, ?_⟩
    · exact hXc.le.trans (Nat.le_floor hX.le)
    · have hh : ((L.image Subtype.val).card : ℝ) ≤ (L.card : ℝ) := by exact_mod_cast hLc.le
      exact hh.trans (by simpa [α] using hL)
    · have hh : ((R.image Subtype.val).card : ℝ) ≤ (R.card : ℝ) := by exact_mod_cast hRc.le
      exact hh.trans (by simpa [α] using hR)
  have hsep := separators_from_connected G Finset.univ α hα s hconnected
  obtain ⟨m, hm, hmbound⟩ := balancing_rounds c hc
  refine ⟨m * s, ?_, ?_⟩
  · have hs : (s : ℝ) ≤ 2 * c := Nat.floor_le (by positivity)
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hmul := mul_le_mul hmbound hs (by positivity) (by positivity)
    push_cast
    nlinarith
  · intro U
    obtain ⟨L, X, R, hp, hn, hX, hL, hR⟩ := balance_iterations G U α hα0 s
      (fun T _ => hsep T (Finset.subset_univ _)) m
    have hpow : α ^ m ≤ (2 / 3 : ℝ) := hm
    rw [max_eq_left hpow] at hL hR
    have hLnat : 3 * L.card ≤ 2 * U.card := by exact_mod_cast (show (3 : ℝ) * L.card ≤ 2 * U.card by linarith)
    have hRnat : 3 * R.card ≤ 2 * U.card := by exact_mod_cast (show (3 : ℝ) * R.card ≤ 2 * U.card by linarith)
    exact ⟨L, X, R, hp, hn, hX, hLnat, hRnat⟩

end SeparatorSubmissionAux.Campbell
namespace SeparatorSubmissionAux.Net

open StableMSR.Recovery

noncomputable def interactionGraph {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (N : Cluster n) : SimpleGraph N :=
  (thresholdGraph d (8 * largestRadius d O) N).induce (N : Set (Point n))

theorem hereditary_growth {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O)
    (W N : Cluster n) (hNW : N ⊆ W)
    (hdiam : diameter d W ≤ densityScale d O (γ - 1))
    (hsep : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → 2 * largestRadius d O < d a b) :
    SeparatorSubmissionAux.Campbell.HereditaryRadiusGrowth
      (interactionGraph d O N) (growthConstant (γ - 1)) := by
  classical
  intro U hU r hr hcenter
  obtain ⟨x, hx⟩ := hcenter
  let B : Cluster n := U.image Subtype.val
  let H : (thresholdGraph d (8 * largestRadius d O) N).Subgraph :=
    (⊤ : (thresholdGraph d (8 * largestRadius d O) N).Subgraph).induce (B : Set (Point n))
  have hBN : B ⊆ N := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    exact z.property
  have hmem : ∀ y : U, y.val.val ∈ H.verts := by
    intro y
    exact Finset.mem_image.mpr ⟨y.val, y.property, rfl⟩
  let f : ((interactionGraph d O N).induce (U : Set N)) →g H.coe :=
    { toFun := fun y => ⟨y.val.val, hmem y⟩
      map_rel' := by intro a b hab; exact ⟨hmem a, hmem b, hab⟩ }
  have hwalk : ∀ y : H.verts, ∃ p : H.coe.Walk (f x) y, p.length ≤ r := by
    intro y
    obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp y.property
    obtain ⟨p, hp⟩ := hU.exists_walk_length_eq_dist x ⟨z, hz⟩
    have heq' : f ⟨z, hz⟩ = y := Subtype.ext heq
    refine ⟨(p.map f).copy rfl heq', ?_⟩
    have hlen : ((p.map f).copy rfl heq').length = p.length := by
      rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
    exact hlen.le.trans (hp.le.trans (hx ⟨z, hz⟩))
  have hbound := StableMSR.Recovery.interaction_subgraph_radius_growth d hd k hk γ hγ hkn O hO W N hNW
    hdiam hsep H (fun y hy => hBN hy) (f x) r hr hwalk
  have hfilter : Finset.univ.filter (fun y => y ∈ H.verts) = B := by
    ext y
    simp [H]
  have hcard : (Finset.univ.filter (fun y => y ∈ H.verts)).card = U.card :=
    (congrArg Finset.card hfilter).trans (Finset.card_image_of_injective _ Subtype.val_injective)
  exact (show (U.card : ℝ) = ((Finset.univ.filter (fun y => y ∈ H.verts)).card : ℝ)
    from congrArg Nat.cast hcard.symm).le.trans hbound

theorem balanced_separators {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O)
    (W N : Cluster n) (hNW : N ⊆ W)
    (hdiam : diameter d W ≤ densityScale d O (γ - 1))
    (hsep : ∀ a ∈ N, ∀ b ∈ N, a ≠ b → 2 * largestRadius d O < d a b) :
    ∃ a : ℕ, 15 * a ≤ widthBound (γ - 1) ∧
      SeparatorSubmissionAux.Havens.HasBalancedSeparations (interactionGraph d O N) a := by
  have hc : 1 ≤ growthConstant (γ - 1) := by
    have he : 0 < γ - 1 := by linarith [hγ.1]
    have h1 : 0 ≤ 80 / (γ - 1) := by positivity
    have h2 : 0 ≤ 80 / (γ - 1) ^ 2 := by positivity
    dsimp [growthConstant]
    linarith
  have hg := hereditary_growth d hd k hk γ hγ hkn O hO W N hNW hdiam hsep
  obtain ⟨a, ha, hs⟩ := SeparatorSubmissionAux.Campbell.hereditary_growth_balanced_separators
    (interactionGraph d O N) (growthConstant (γ - 1)) hc hg
  refine ⟨a, ?_, hs⟩
  have hceil := Nat.le_ceil (49 * growthConstant (γ - 1) ^ 2 + 30 * growthConstant (γ - 1))
  change 15 * a ≤ ⌈49 * growthConstant (γ - 1) ^ 2 + 30 * growthConstant (γ - 1)⌉₊
  exact_mod_cast ha.trans hceil

end SeparatorSubmissionAux.Net

theorem solution {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (k : ℕ) (hk : 1 ≤ k ∧ k ≤ n) (γ : ℝ) (hγ : 1 < γ ∧ γ < 2) (hkn : k < n)
    (O : Partition n) (hO : Stable d k γ O)
    (W N : Cluster n) (hNW : N ⊆ W)
    (hdiam : diameter d W ≤ densityScale d O (γ - 1))
    (hsep : ∀ x ∈ N, ∀ y ∈ N, x ≠ y → 2 * largestRadius d O < d x y) :
    ∃ a : ℕ, 15 * a ≤ widthBound (γ - 1) ∧
      ∀ U : Finset N, ∃ L S T : Finset N,
        (Disjoint L S ∧ Disjoint L T ∧ Disjoint S T ∧ L ∪ S ∪ T = U) ∧
        (∀ x ∈ L, ∀ y ∈ T, ¬ (thresholdGraph d (8 * largestRadius d O) N).Adj x y) ∧
        S.card ≤ a ∧ 3 * L.card ≤ 2 * U.card ∧ 3 * T.card ≤ 2 * U.card := by
  exact SeparatorSubmissionAux.Net.balanced_separators d hd k hk γ hγ hkn O hO W N hNW hdiam hsep

