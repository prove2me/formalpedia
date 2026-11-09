-- Prove2me | solution 1 for TenChallenges.challenge_05_r3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:51:53.321202+00:00
-- url     : https://prove2.me/submissions/7118857e-48d8-4739-94e2-c9e24ae55136

import Definitions.Def_TenChallenges_Challenge_05
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open SimpleGraph

namespace Aux_TC05_R3

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma adj_trans_of_no_P3 (hfree : ¬ pathGraph 3 ⊴ G) {u v w : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : u ≠ w) : G.Adj u w := by
  by_contra hnot
  apply hfree
  have h1 : u ≠ v := G.ne_of_adj huv
  have h2 : v ≠ w := G.ne_of_adj hvw
  refine ⟨{ toFun := ![u, v, w], inj' := ?_, map_rel_iff' := ?_ }⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [h1, h1.symm, h2, h2.symm, huw, huw.symm]
  · intro i j
    change G.Adj (![u, v, w] i) (![u, v, w] j) ↔ (pathGraph 3).Adj i j
    fin_cases i <;> fin_cases j <;>
      simp [pathGraph, huv, huv.symm, hvw, hvw.symm, hnot,
        show ¬G.Adj w u from fun h => hnot h.symm]

def closedNhd (x : V) : Finset V :=
  Finset.univ.filter (fun y => y = x ∨ G.Adj x y)

lemma isClique_closedNhd (hfree : ¬ pathGraph 3 ⊴ G) (x : V) :
    G.IsClique (closedNhd G x : Set V) := by
  intro y hy z hz hyz
  simp only [closedNhd, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy hz
  rcases hy with rfl | hxy
  · rcases hz with rfl | hxz
    · exact absurd rfl hyz
    · exact hxz
  · rcases hz with rfl | hxz
    · exact hxy.symm
    · exact adj_trans_of_no_P3 G hfree hxy.symm hxz hyz

end Aux_TC05_R3

open Aux_TC05_R3 TenChallenges in
/-- The path on three vertices has Erdős–Hajnal exponent `1/2`. -/
theorem solution : statement_05 3 := by
  classical
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro V _ G hfree
  let indepFam : Finset (Finset V) :=
    Finset.univ.filter (fun s : Finset V => Gᶜ.IsClique (s : Set V))
  have hindep_ne : indepFam.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
  obtain ⟨I, hI_mem, hI_max⟩ := Finset.exists_max_image indepFam Finset.card hindep_ne
  have hI_clique : Gᶜ.IsClique (I : Set V) := (Finset.mem_filter.mp hI_mem).2
  have hcov : (Finset.univ : Finset V) ⊆ I.biUnion (closedNhd G) := by
    intro v _
    rw [Finset.mem_biUnion]
    by_contra hnot
    push_neg at hnot
    have hvI : v ∉ I := by
      intro hv
      exact hnot v hv (by simp [closedNhd])
    have hv_ins : Gᶜ.IsClique (insert v I : Finset V) := by
      rw [Finset.coe_insert, isClique_insert]
      refine ⟨hI_clique, fun x hx hxv => ?_⟩
      have hxnot := hnot x hx
      simp only [closedNhd, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hxnot
      rw [compl_adj]
      exact ⟨hxv, fun hadj => hxnot.2 hadj.symm⟩
    have hle := hI_max (insert v I) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_ins⟩)
    rw [Finset.card_insert_of_notMem hvI] at hle
    omega
  by_cases hI_ne : I.Nonempty
  · obtain ⟨x₀, hx₀_mem, hx₀_max⟩ := Finset.exists_max_image I (fun x => (closedNhd G x).card) hI_ne
    have hcard_le : Fintype.card V ≤ I.card * (closedNhd G x₀).card := by
      calc Fintype.card V = (Finset.univ : Finset V).card := (Finset.card_univ).symm
        _ ≤ (I.biUnion (closedNhd G)).card := Finset.card_le_card hcov
        _ ≤ ∑ x ∈ I, (closedNhd G x).card := Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ I, (closedNhd G x₀).card := Finset.sum_le_sum fun x hx => hx₀_max x hx
        _ = I.card * (closedNhd G x₀).card := by simp
    let M : ℕ := max I.card (closedNhd G x₀).card
    have hM_sq : (Fintype.card V : ℝ) ≤ (M : ℝ) ^ (2 : ℝ) := by
      have h1 : Fintype.card V ≤ M * M := by
        calc Fintype.card V ≤ I.card * (closedNhd G x₀).card := hcard_le
          _ ≤ M * M := Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
      have h2 : (Fintype.card V : ℝ) ≤ (M : ℝ) * (M : ℝ) := by exact_mod_cast h1
      simpa [Real.rpow_two, sq] using h2
    have hM_rpow : (Fintype.card V : ℝ) ^ (1 / 2 : ℝ) ≤ (M : ℝ) := by
      calc (Fintype.card V : ℝ) ^ (1 / 2 : ℝ)
          ≤ ((M : ℝ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hM_sq (by norm_num)
        _ = (M : ℝ) ^ ((2 : ℝ) * (1 / 2 : ℝ)) :=
            (Real.rpow_mul (Nat.cast_nonneg M) 2 (1 / 2)).symm
        _ = (M : ℝ) := by norm_num
    rcases le_total I.card (closedNhd G x₀).card with hle | hle
    · have hM_eq : M = (closedNhd G x₀).card := max_eq_right hle
      refine ⟨closedNhd G x₀, Or.inl (isClique_closedNhd G hfree x₀), ?_⟩
      rw [← hM_eq]
      exact hM_rpow
    · have hM_eq : M = I.card := max_eq_left hle
      refine ⟨I, Or.inr hI_clique, ?_⟩
      rw [← hM_eq]
      exact hM_rpow
  · rw [Finset.not_nonempty_iff_eq_empty] at hI_ne
    have huniv_empty : (Finset.univ : Finset V) = ∅ := by
      apply Finset.subset_empty.mp
      simpa [hI_ne] using hcov
    have hcard0 : Fintype.card V = 0 := by
      rw [← Finset.card_univ, huniv_empty, Finset.card_empty]
    refine ⟨∅, Or.inl (by simp), ?_⟩
    simp [hcard0]
