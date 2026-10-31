-- Prove2me | solution 1 for WilliamsonShmoys.band_treewidth_ram_solver
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @amirh
-- created : 2026-10-30T23:34:09.873544+00:00
-- url     : https://prove2.me/submissions/e47c129a-1cfd-4e86-8267-c7d90818ddfa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_WilliamsonShmoys_treewidth_mwis_ram_solver
import Theorems.Thm_WilliamsonShmoys_baker_shifting_ram_reduction

set_option autoImplicit false
open scoped BigOperators
open WilliamsonShmoys

theorem solution :
    ∃ (program : List PlanarRAMInstruction) (C d : ℕ),
      0 < C ∧ 0 < d ∧
      ∀ (k : ℕ), 0 < k →
      ∀ (n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        let G := SimpleGraph.fromRel (fun u v => edge u v = true)
        (∀ j < k, RobertsonSeymour1986.GM5.TreewidthLE
          (G.induce {v : Fin n | bakerLevel G v % k ≠ j}) (3 * k)) →
        ∃ t : ℕ, t + 1 ≤ C * 2 ^ (d * k) * (n + 1) ^ 2 ∧
          let result := planarRAMRun program (planarRAMInput n k edge weight) t
          program[result.pc]? = some PlanarRAMInstruction.halt ∧
          (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
          G.IsIndepSet (planarRAMOutput n result : Set (Fin n)) ∧
          ∀ j < k, ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
            (∀ v ∈ S, bakerLevel G v % k ≠ j) →
            ∑ i ∈ S, weight i ≤ ∑ i ∈ planarRAMOutput n result, weight i := by
  -- Child 1: an exact max-weight independent-set program for tree-width ≤ w.
  obtain ⟨solver, C₀, d₀, hC₀, hd₀, hsolver⟩ := treewidth_mwis_ram_solver
  -- Child 2: Baker's shifting wrapper turns any such program into the band solver.
  exact baker_shifting_ram_reduction solver C₀ d₀ hC₀ hd₀ hsolver
