-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.cut_vertex_two_side_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:35:04.313071+00:00
-- url     : https://prove2.me/submissions/004f06d5-d156-4d87-8ccb-3eb5e5ee08e6

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_largestInducedTreeSize_induce_le
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_geodesic_branches_bound_of_not_reachable
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_eq_add_of_not_reachable_compl
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_connected_induce_cutSide
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_radius_le_radius_induce_of_dominated
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_not_connected_induce_delete_of_separated_pair

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    (hr : 2 ≤ G.radius.toNat) (hlt : largestInducedTreeSize G < 2 * G.radius.toNat)
    (hsmall : ∀ (S : Set α) [DecidablePred (· ∈ S)], S ≠ Set.univ →
      (G.induce S).Connected →
      (∃ x, ¬ ((G.induce S).induce ({x}ᶜ : Set S)).Connected) →
      2 * (G.induce S).radius.toNat ≤ largestInducedTreeSize (G.induce S))
    (c : α) (hc : ¬ (G.induce ({c}ᶜ : Set α)).Connected) :
    ∃ a b : ↥({c}ᶜ : Set α), ∃ q : G.Walk c (b : α),
      q.length = G.dist c b ∧
      ¬ (G.induce ({c}ᶜ : Set α)).Reachable a b ∧
      G.dist c b + 2 ≤ G.dist c a ∧
      ∀ z : α, z ∈ cutSide G c a ∨ z ∈ q.support := by
  classical
  obtain ⟨a, ha⟩ := G.exists_edist_eq_eccent_of_finite c
  have hra : G.radius.toNat ≤ G.dist c a :=
    ENat.toNat_le_toNat (ha ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG c a))
  have hac : a ≠ c := by intro heq; subst a; simp only [dist_self] at hra; omega
  let H := G.induce ({c}ᶜ : Set α)
  let a' : ↥({c}ᶜ : Set α) := ⟨a, by simpa using hac⟩
  have hbex : ∃ b : ↥({c}ᶜ : Set α), ¬ H.Reachable a' b := by
    by_contra! hall
    exact hc ((H.connected_iff_exists_forall_reachable).mpr ⟨a', hall⟩)
  let B : Set ↥({c}ᶜ : Set α) := {b | ¬ H.Reachable a' b}
  obtain ⟨b, hb, hbmax⟩ := Set.exists_max_image B (fun z => G.dist c (z : α))
    (Set.toFinite B) hbex
  have hbc : (b : α) ≠ c := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using b.property
  have hbranches := geodesic_branches_bound_of_not_reachable hG hac hbc hb
  have hgap : G.dist c b + 2 ≤ G.dist c a := by omega
  obtain ⟨q, _, hq⟩ := hG.exists_path_of_dist c (b : α)
  let S := cutSide G c a'
  let U := S ∪ {z : α | z ∈ q.support}
  have hcS : c ∈ S := Or.inl rfl
  have haS : a ∈ S := Or.inr ⟨hac, Reachable.rfl⟩
  have hU : (G.induce U).Connected :=
    induce_union_connected (connected_induce_cutSide hG c a').preconnected
      q.connected_induce_support.preconnected ⟨c, hcS, q.start_mem_support⟩
  have hcU : c ∈ U := Or.inl hcS
  have haU : a ∈ U := Or.inl haS
  have hbU : (b : α) ∈ U := Or.inr q.end_mem_support
  have hcutU := not_connected_induce_delete_of_separated_pair hcU haU hbU hac hbc hb
  have hdepth (z : α) : G.dist c z ≤ G.dist c a := by
    have hle : G.edist c z ≤ G.edist c a := by rw [ha]; exact G.edist_le_eccent
    exact ENat.toNat_le_toNat hle (edist_ne_top_iff_reachable.mpr (hG c a))
  have hdom : ∀ v ∈ U, ∀ z ∉ U, ∃ w ∈ U, G.dist v z ≤ G.dist v w := by
    intro v _ z hz
    have hzS : z ∉ S := fun hzS => hz (Or.inl hzS)
    have hzc : z ≠ c := by intro heq; exact hzS (heq ▸ hcS)
    have hznr : ¬ H.Reachable a'
        ⟨z, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc⟩ :=
      fun hreach => hzS (Or.inr ⟨hzc, hreach⟩)
    have hzb : G.dist c z ≤ G.dist c b := hbmax _ hznr
    by_cases hvS : v ∈ S
    · refine ⟨b, hbU, ?_⟩
      have hvb : G.dist v b = G.dist v c + G.dist c b := by
        by_cases hvc : v = c
        · simp [hvc]
        · rcases hvS with heq | ⟨_, hvr⟩
          · exact (hvc heq).elim
          · apply dist_eq_add_of_not_reachable_compl hG hvc hbc
            intro hreach
            exact hb (hvr.trans hreach)
      have htri := hG.dist_triangle (u := v) (v := c) (w := z)
      omega
    · refine ⟨a, haU, ?_⟩
      have hvc : v ≠ c := by intro heq; exact hvS (heq ▸ hcS)
      have hva : G.dist v a = G.dist v c + G.dist c a := by
        apply dist_eq_add_of_not_reachable_compl hG hvc hac
        intro hreach
        exact hvS (Or.inr ⟨hvc, hreach.symm⟩)
      have htri := hG.dist_triangle (u := v) (v := c) (w := z)
      have hzdepth := hdepth z
      omega
  have hUeq : U = Set.univ := by
    by_contra hproper
    have hsm := hsmall U hproper hU ⟨⟨c, hcU⟩, hcutU⟩
    have hrad := radius_le_radius_induce_of_dominated hG U hU hdom
    have htrans := largestInducedTreeSize_induce_le G U
    omega
  refine ⟨a', b, q, hq, hb, hgap, ?_⟩
  intro z
  have hz : z ∈ U := hUeq ▸ Set.mem_univ z
  exact hz
end WrittenOnTheWallII.GraphConjecture84
