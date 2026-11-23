-- Prove2me | solution 1 for TenChallenges.challenge_06_r2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-23T11:42:42.677128+00:00
-- url     : https://prove2.me/submissions/0fd048f9-502c-4a04-b775-68d7959a505e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Order.Filter.AtTopBot.Finite
import Definitions.Def_TenChallenges_Challenge_06
import Theorems.Thm_TenChallenges_wagner_isPlanar
import Theorems.Thm_TenChallenges_bounded_treewidth_sets_wqo
import Theorems.Thm_TenChallenges_planar_sets_increasing_treewidth_wqo
import Theorems.Thm_RobertsonSeymour1986_GM5_excluding_planar_graph
import Theorems.Thm_RobertsonSeymour1986_GM5_planar_isMinor_grid

universe u

open Classical Filter

namespace TenChallenges.R2TW

/-- The branch-set model of Graph Minors V gives minor data in the sense of `SimpleGraph.Minor`. -/
theorem minor_of_isMinor {W V : Type} {H : SimpleGraph W} {G : SimpleGraph V}
    (h : RobertsonSeymour1986.GM5.IsMinor H G) : Nonempty (SimpleGraph.Minor H G) := by
  obtain ⟨β, hβ, hdisj, hadj⟩ := h
  exact ⟨{ branchSet := β
           pairwise_disjoint_branchSet := hdisj
           connectedOn_branchSet := fun w => (hβ w).2
           exists_mem_branchSet_of_adj := fun a b hab => hadj a b hab }⟩

section
variable {Q : Type u} (le : Q → Q → Prop)

theorem leStar_zero_zero (X Y : VStar Q 0) :
    leStar le 0 X 0 Y ↔ le (cast (VStar_zero Q) X) (cast (VStar_zero Q) Y) := by
  unfold leStar
  simp only [Ordinal.limitRecOn_zero]

theorem leStar_succ_succ (α : Ordinal.{u}) (X : VStar Q (Order.succ α)) (β : Ordinal.{u})
    (Y : VStar Q (Order.succ β)) :
    leStar le (Order.succ α) X (Order.succ β) Y ↔
      ∀ x ∈ (cast (VStar_succ Q α) X).val,
        ∃ y ∈ (cast (VStar_succ Q β) Y).val, leStar le α x β y := by
  conv_lhs => unfold leStar
  simp only [Ordinal.limitRecOn_succ]
  rfl

end

/-- Graphs excluding a fixed finite planar graph have bounded tree-width. -/
theorem exists_treewidth_bound (P : PlanarGraph) : ∃ c : ℕ, ∀ G : PlanarGraph,
    ¬ PlanarGraph.MinorLE P G → RobertsonSeymour1986.GM5.TreewidthLE G.val.2 c := by
  let H := P.val.2
  have hH : RobertsonSeymour1986.GM5.IsPlanar H := wagner_isPlanar H P.property
  have hne : ∃ t, Even t ∧ 6 ≤ t ∧ RobertsonSeymour1986.GM5.IsMinor H
      (RobertsonSeymour1986.GM5.grid t) :=
    RobertsonSeymour1986.GM5.planar_isMinor_grid H hH
  have hθ : IsLeast {t : ℕ | Even t ∧ 6 ≤ t ∧
      RobertsonSeymour1986.GM5.IsMinor H (RobertsonSeymour1986.GM5.grid t)} (Nat.find hne) :=
    ⟨Nat.find_spec hne, fun t ht => Nat.find_min' hne ht⟩
  exact ⟨_, fun G hG => RobertsonSeymour1986.GM5.excluding_planar_graph H hH _ hθ _
    (fun hm => hG (minor_of_isMinor hm))⟩

/-- Sequences of sets of planar graphs, each of bounded tree-width. -/
theorem bounded_sets (Y : ℕ → Set PlanarGraph)
    (hY : ∀ n, ∃ c, ∀ G ∈ Y n, RobertsonSeymour1986.GM5.TreewidthLE G.val.2 c) :
    ∃ i j, i < j ∧ ∀ G ∈ Y i, ∃ H ∈ Y j, PlanarGraph.MinorLE G H := by
  let c : ℕ → ℕ := fun n => Nat.find (hY n)
  have hc : ∀ n, ∀ G ∈ Y n, RobertsonSeymour1986.GM5.TreewidthLE G.val.2 (c n) :=
    fun n => Nat.find_spec (hY n)
  by_cases hT : Tendsto c atTop atTop
  · obtain ⟨φ, hφ, hcφ⟩ := strictMono_subseq_of_tendsto_atTop hT
    obtain ⟨i, j, hij, h⟩ := planar_sets_increasing_treewidth_wqo (c ∘ φ) hcφ (Y ∘ φ)
      (fun n => hc (φ n)) (fun n => by
        have := Nat.find_min (hY (φ (n + 1))) (hcφ (Nat.lt_succ_self n))
        push Not at this
        exact this)
    exact ⟨φ i, φ j, hφ hij, h⟩
  · rw [tendsto_atTop] at hT
    push Not at hT
    obtain ⟨b, hb⟩ := hT
    obtain ⟨φ, hφ, hcφ⟩ := extraction_of_frequently_atTop hb
    have mono : ∀ n, ∀ G ∈ Y (φ n), RobertsonSeymour1986.GM5.TreewidthLE G.val.2 b := by
      intro n G hG
      obtain ⟨T, hTf, t, Z, hZ, hcard⟩ := hc _ G hG
      refine ⟨T, hTf, t, Z, hZ, fun s => (hcard s).trans ?_⟩
      have := hcφ n
      omega
    obtain ⟨i, j, hij, h⟩ := bounded_treewidth_sets_wqo b (fun n => Subtype.val '' Y (φ n)) (by
      rintro n _ ⟨G, hG, rfl⟩
      exact mono n G hG)
    refine ⟨φ i, φ j, hφ hij, fun G hG => ?_⟩
    obtain ⟨_, ⟨H, hH, rfl⟩, hGH⟩ := h G.val ⟨G, hG, rfl⟩
    exact ⟨H, hH, hGH⟩

/-- Sets of planar graphs are well-quasi-ordered under the lifted minor relation. -/
theorem planar_sets_wqo (X : ℕ → Set PlanarGraph) :
    ∃ i j, i < j ∧ ∀ G ∈ X i, ∃ H ∈ X j, PlanarGraph.MinorLE G H := by
  by_cases hex : ∃ j, 0 < j ∧ ∀ G ∈ X 0, ∃ H ∈ X j, PlanarGraph.MinorLE G H
  · obtain ⟨j, hj, h⟩ := hex
    exact ⟨0, j, hj, h⟩
  · push Not at hex
    obtain ⟨i, j, hij, h⟩ := bounded_sets (fun n => X (n + 1)) (fun n => by
      obtain ⟨P, _, hP⟩ := hex (n + 1) n.succ_pos
      obtain ⟨c, hc⟩ := exists_treewidth_bound P
      exact ⟨c, fun G hG => hc G (hP G hG)⟩)
    exact ⟨i + 1, j + 1, by omega, h⟩

end TenChallenges.R2TW

open TenChallenges.R2TW in
theorem solution : TenChallenges.statement_06 2 := by
  have hmod : (2 : Ordinal) % 2 = 0 := Ordinal.mod_self 2
  have hdiv : (2 : Ordinal) / 2 = Order.succ 0 := by
    rw [Ordinal.div_self two_ne_zero, Order.succ_eq_add_one, zero_add]
  unfold TenChallenges.statement_06
  rw [if_pos hmod, hdiv]
  intro f
  obtain ⟨i, j, hij, h⟩ := planar_sets_wqo fun n =>
    (fun x => cast (VStar_zero PlanarGraph) x) '' (cast (VStar_succ PlanarGraph 0) (f n)).val
  refine ⟨i, j, hij, (leStar_succ_succ _ _ _ _ _).2 fun x hx => ?_⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := h _ ⟨x, hx, rfl⟩
  exact ⟨y, hy, (leStar_zero_zero _ _ _).2 hxy⟩
