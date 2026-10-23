-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P10.opennessLiftedSubnets
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:14:07.827985+00:00
-- url     : https://prove2.me/submissions/24516790-2db3-4c7a-95d0-ff54e37c479b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P10

noncomputable section

open Set Filter TopologicalSpace

open scoped Topology

universe u v w

namespace QAlgorithms.Papers.Independent.Frontier18.P10

/-- index set for the lifted subnet -/
def x8S {X : Type u} {Y : Type v} [TopologicalSpace X] (phi : X → Y) (x0 : X) (y : ℕ → Y) :
    Type u := {p : Set X × ℕ // p.1 ∈ 𝓝 x0 ∧ y p.2 ∈ phi '' p.1}

lemma x8_back {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] (phi : X → Y)
    (h : LiftedSubnetProperty phi) : IsOpenMap phi := by
  rw [isOpenMap_iff_nhds_le]
  intro x0 U hU
  rw [Filter.mem_map] at hU
  by_contra hn
  -- build a sequence avoiding phi '' (phi ⁻¹' U)
  have hball : ∀ n : ℕ, ∃ z, dist z (phi x0) < 1 / ((n : ℝ) + 1) ∧ z ∉ U := by
    intro n
    by_contra hc
    push_neg at hc
    apply hn
    refine Metric.mem_nhds_iff.2 ⟨1 / ((n : ℝ) + 1), by positivity, fun z hz => hc z hz⟩
  choose z hz1 hz2 using hball
  have hzt : Tendsto z atTop (𝓝 (phi x0)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => (hz1 n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨D, ord, hne, hdir, idx, x, _, hx, hphi⟩ := h x0 z hzt
  letI : Preorder D := ord
  haveI : NeBot (atTop : Filter D) := atTop_neBot
  have hm : ∀ᶠ d in (atTop : Filter D), x d ∈ phi ⁻¹' U := hx hU
  obtain ⟨d, hd⟩ := hm.exists
  exact hz2 (idx d) (by rw [← hphi d]; exact hd)

lemma x8_fwd {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] (phi : X → Y)
    (h : IsOpenMap phi) : LiftedSubnetProperty phi := by
  intro x0 y hy
  have hev : ∀ U ∈ 𝓝 x0, ∀ N : ℕ, ∃ m, N ≤ m ∧ y m ∈ phi '' U := by
    intro U hU N
    have := (hy.eventually (h.image_mem_nhds hU)).and (eventually_ge_atTop N)
    obtain ⟨m, hm1, hm2⟩ := this.exists
    exact ⟨m, hm2, hm1⟩
  let D := ULift.{v} (x8S phi x0 y)
  let f : D → (Set X)ᵒᵈ × ℕ := fun d => (OrderDual.toDual d.down.1.1, d.down.1.2)
  letI ord : Preorder D := Preorder.lift f
  have hle : ∀ a b : D, a ≤ b ↔ b.down.1.1 ⊆ a.down.1.1 ∧ a.down.1.2 ≤ b.down.1.2 := by
    intro a b; exact Iff.rfl
  have hmk : ∀ U ∈ 𝓝 x0, ∀ N : ℕ, ∃ d : D, d.down.1.1 = U ∧ N ≤ d.down.1.2 := by
    intro U hU N
    obtain ⟨m, hm, hym⟩ := hev U hU N
    exact ⟨⟨⟨(U, m), hU, hym⟩⟩, rfl, hm⟩
  have hdir : IsDirectedOrder D := by
    constructor
    intro a b
    obtain ⟨c, hc1, hc2⟩ := hmk (a.down.1.1 ∩ b.down.1.1)
      (inter_mem a.down.2.1 b.down.2.1) (max a.down.1.2 b.down.1.2)
    refine ⟨c, (hle _ _).2 ⟨?_, ?_⟩, (hle _ _).2 ⟨?_, ?_⟩⟩
    · rw [hc1]; exact inter_subset_left
    · exact le_trans (le_max_left _ _) hc2
    · rw [hc1]; exact inter_subset_right
    · exact le_trans (le_max_right _ _) hc2
  have hne : Nonempty D := by
    obtain ⟨d, _⟩ := hmk univ univ_mem 0
    exact ⟨d⟩
  have hpre : ∀ d : D, ∃ p ∈ d.down.1.1, phi p = y d.down.1.2 := fun d => d.down.2.2
  choose x hx1 hx2 using hpre
  refine ⟨D, ord, hne, hdir, fun d => d.down.1.2, x, ?_, ?_, fun d => hx2 d⟩
  · rw [tendsto_atTop_atTop]
    intro N
    obtain ⟨d0, _, hd0⟩ := hmk univ univ_mem N
    exact ⟨d0, fun d hd => le_trans hd0 ((hle _ _).1 hd).2⟩
  · intro W hW
    rw [Filter.mem_map, mem_atTop_sets]
    obtain ⟨d0, hd0, _⟩ := hmk W hW 0
    refine ⟨d0, fun d hd => ?_⟩
    have := ((hle _ _).1 hd).1
    rw [hd0] at this
    exact this (hx1 d)

end QAlgorithms.Papers.Independent.Frontier18.P10

open QAlgorithms.Papers.Independent.Frontier18.P10 in
theorem solution {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] (phi : X → Y) :
    IsOpenMap phi ↔ LiftedSubnetProperty phi :=
  ⟨x8_fwd phi, x8_back phi⟩
