-- Prove2me | solution 3 for TenChallenges.challenge_06_r0
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Davide
-- created : 2026-11-18T12:24:20.427632+00:00
-- url     : https://prove2.me/submissions/6ef0c1fd-ea5c-4880-a0e2-803a61a78e9c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_TenChallenges_Challenge_06
import Theorems.Thm_TenChallenges_wagner_isPlanar
import Theorems.Thm_TenChallenges_bounded_treewidth_wqo
import Theorems.Thm_RobertsonSeymour1986_GM5_excluding_planar_graph
import Theorems.Thm_RobertsonSeymour1986_GM5_planar_isMinor_grid

open Classical

namespace TenChallenges.R0GM

/-- The branch-set model of Graph Minors V gives minor data in the sense of `SimpleGraph.Minor`. -/
theorem minor_of_isMinor {W V : Type} {H : SimpleGraph W} {G : SimpleGraph V}
    (h : RobertsonSeymour1986.GM5.IsMinor H G) : Nonempty (SimpleGraph.Minor H G) := by
  obtain ⟨β, hβ, hdisj, hadj⟩ := h
  exact ⟨{ branchSet := β
           pairwise_disjoint_branchSet := hdisj
           connectedOn_branchSet := fun w => (hβ w).2
           exists_mem_branchSet_of_adj := fun a b hab => hadj a b hab }⟩

theorem leStar_zero_zero {Q : Type} (le : Q → Q → Prop) (X Y : VStar Q 0) :
    leStar le 0 X 0 Y ↔ le (cast (VStar_zero Q) X) (cast (VStar_zero Q) Y) := by
  unfold leStar
  simp only [Ordinal.limitRecOn_zero]

/-- Finite planar graphs are well-quasi-ordered by minors. -/
theorem planar_wqo (g : ℕ → PlanarGraph) :
    ∃ i j, i < j ∧ PlanarGraph.MinorLE (g i) (g j) := by
  by_cases hex : ∃ j, 0 < j ∧ PlanarGraph.MinorLE (g 0) (g j)
  · obtain ⟨j, hj, h⟩ := hex
    exact ⟨0, j, hj, h⟩
  · push_neg at hex
    let H := (g 0).val.2
    have hH : RobertsonSeymour1986.GM5.IsPlanar H := wagner_isPlanar H (g 0).property
    have hne : ∃ t, Even t ∧ 6 ≤ t ∧ RobertsonSeymour1986.GM5.IsMinor H
        (RobertsonSeymour1986.GM5.grid t) :=
      RobertsonSeymour1986.GM5.planar_isMinor_grid H hH
    have hθ : IsLeast {t : ℕ | Even t ∧ 6 ≤ t ∧
        RobertsonSeymour1986.GM5.IsMinor H (RobertsonSeymour1986.GM5.grid t)} (Nat.find hne) :=
      ⟨Nat.find_spec hne, fun t ht => Nat.find_min' hne ht⟩
    have htw : ∀ n, RobertsonSeymour1986.GM5.TreewidthLE (g (n + 1)).val.2
        (RobertsonSeymour1986.GM5.theta9 (Nat.find hne)) := fun n =>
      RobertsonSeymour1986.GM5.excluding_planar_graph H hH _ hθ _
        (fun hm => hex (n + 1) (Nat.succ_pos n) (minor_of_isMinor hm))
    obtain ⟨i, j, hij, h⟩ := bounded_treewidth_wqo _ (fun n => (g (n + 1)).val) htw
    exact ⟨i + 1, j + 1, by omega, h⟩

end TenChallenges.R0GM

open TenChallenges.R0GM in
theorem solution : TenChallenges.statement_06 0 := by
  unfold TenChallenges.statement_06
  rw [if_pos (Ordinal.zero_mod 2), Ordinal.zero_div]
  intro f
  obtain ⟨i, j, hij, h⟩ := planar_wqo (fun n => cast (VStar_zero _) (f n))
  exact ⟨i, j, hij, (leStar_zero_zero _ _ _).2 h⟩
