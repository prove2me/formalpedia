-- Prove2me | solution 2 for WilliamsonShmoys.baker_masked_best_of_runs_ram
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T11:22:28.84312+00:00
-- url     : https://prove2.me/submissions/d3f4e672-df43-414b-b361-7886b66aafe2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_WilliamsonShmoys_treewidth_disjoint_union_le
import Theorems.Thm_WilliamsonShmoys_baker_union_single_call_ram

set_option autoImplicit false
open scoped BigOperators

theorem solution
    (solver : List WilliamsonShmoys.PlanarRAMInstruction) (C₀ d₀ : ℕ) (hC₀ : 0 < C₀) (hd₀ : 0 < d₀)
    (hsolver : ∀ (w n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
      let G := SimpleGraph.fromRel (fun u v => edge u v = true)
      RobertsonSeymour1986.GM5.TreewidthLE G w →
      ∃ t : ℕ, t + 1 ≤ C₀ * 2 ^ (d₀ * w) * (n + 1) ^ 2 ∧
        let result := WilliamsonShmoys.planarRAMRun solver (WilliamsonShmoys.planarRAMInput n w edge weight) t
        solver[result.pc]? = some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
        (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
        G.IsIndepSet (WilliamsonShmoys.planarRAMOutput n result : Set (Fin n)) ∧
        ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
          ∑ i ∈ S, weight i ≤ ∑ i ∈ WilliamsonShmoys.planarRAMOutput n result, weight i) :
    ∃ (program : List WilliamsonShmoys.PlanarRAMInstruction) (C d : ℕ),
      0 < C ∧ 0 < d ∧
      ∀ (k : ℕ), 0 < k →
      ∀ (n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        let G := SimpleGraph.fromRel (fun u v => edge u v = true)
        (∀ j < k, RobertsonSeymour1986.GM5.TreewidthLE
          (SimpleGraph.fromRel (fun u v => G.Adj u v ∧
            WilliamsonShmoys.bakerLevel G u % k ≠ j ∧ WilliamsonShmoys.bakerLevel G v % k ≠ j))
          (3 * k)) →
        ∃ t : ℕ, t + 1 ≤ C * 2 ^ (d * k) * (n + 1) ^ 2 ∧
          let result := WilliamsonShmoys.planarRAMRun program (WilliamsonShmoys.planarRAMInput n k edge weight) t
          program[result.pc]? = some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
          (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
          G.IsIndepSet (WilliamsonShmoys.planarRAMOutput n result : Set (Fin n)) ∧
          ∀ j < k, ∀ S : Finset (Fin n),
            (SimpleGraph.fromRel (fun u v => G.Adj u v ∧
              WilliamsonShmoys.bakerLevel G u % k ≠ j ∧ WilliamsonShmoys.bakerLevel G v % k ≠ j)).IsIndepSet
              (S : Set (Fin n)) →
            ∑ i ∈ S, (if WilliamsonShmoys.bakerLevel G i % k ≠ j then weight i else 0) ≤
              ∑ i ∈ WilliamsonShmoys.planarRAMOutput n result, weight i := by
  obtain ⟨program, C, d, hC, hd, hprog⟩ :=
    WilliamsonShmoys.baker_union_single_call_ram solver C₀ d₀ hC₀ hd₀ hsolver
  refine ⟨program, C, d, hC, hd, ?_⟩
  intro k hk n edge weight G htw
  apply hprog k hk n edge weight
  have hU := WilliamsonShmoys.treewidth_disjoint_union_le (m := k) (n := n)
    (fun j => SimpleGraph.fromRel (fun u v => G.Adj u v ∧
      WilliamsonShmoys.bakerLevel G u % k ≠ j.val ∧ WilliamsonShmoys.bakerLevel G v % k ≠ j.val))
    (3 * k) (fun j => htw j.val j.isLt)
  have heq : (SimpleGraph.fromRel (fun (x y : Fin k × Fin n) => x.1 = y.1 ∧
      G.Adj x.2 y.2 ∧ WilliamsonShmoys.bakerLevel G x.2 % k ≠ x.1.val ∧
        WilliamsonShmoys.bakerLevel G y.2 % k ≠ x.1.val)) =
      SimpleGraph.fromRel (fun (u v : Fin k × Fin n) => u.1 = v.1 ∧
        (SimpleGraph.fromRel (fun a b => G.Adj a b ∧
          WilliamsonShmoys.bakerLevel G a % k ≠ u.1.val ∧
            WilliamsonShmoys.bakerLevel G b % k ≠ u.1.val)).Adj u.2 v.2) := by
    ext x y
    simp only [SimpleGraph.fromRel_adj, ne_eq, Prod.ext_iff]
    have hs : ∀ a b, G.Adj a b → G.Adj b a := fun a b h => h.symm
    have hne : ∀ a b, G.Adj a b → a ≠ b := fun a b h => G.ne_of_adj h
    constructor
    · rintro ⟨hxy, (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)⟩
      · exact ⟨hxy, Or.inl ⟨h1, hne _ _ h2, Or.inl ⟨h2, h3, h4⟩⟩⟩
      · exact ⟨hxy, Or.inr ⟨h1, hne _ _ h2, Or.inl ⟨h2, h3, h4⟩⟩⟩
    · rintro ⟨hxy, (⟨h1, -, (⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩)⟩ | ⟨h1, -, (⟨h2, h3, h4⟩ | ⟨h2, h3, h4⟩)⟩)⟩
      · exact ⟨hxy, Or.inl ⟨h1, h2, h3, h4⟩⟩
      · exact ⟨hxy, Or.inr ⟨h1.symm, h2, by rw [← h1]; exact h3, by rw [← h1]; exact h4⟩⟩
      · exact ⟨hxy, Or.inr ⟨h1, h2, h3, h4⟩⟩
      · exact ⟨hxy, Or.inl ⟨h1.symm, h2, by rw [← h1]; exact h3, by rw [← h1]; exact h4⟩⟩
  rw [heq]
  exact hU
