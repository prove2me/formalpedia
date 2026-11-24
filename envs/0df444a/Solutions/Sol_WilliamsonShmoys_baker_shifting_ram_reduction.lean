-- Prove2me | solution 1 for WilliamsonShmoys.baker_shifting_ram_reduction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T05:56:06.739233+00:00
-- url     : https://prove2.me/submissions/572e24ab-2323-45ea-9710-e04f45c2c465
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_WilliamsonShmoys_treewidth_masked_of_induced
import Theorems.Thm_WilliamsonShmoys_baker_masked_best_of_runs_ram

set_option autoImplicit false
open scoped BigOperators
open WilliamsonShmoys

theorem solution
    (solver : List PlanarRAMInstruction) (C₀ d₀ : ℕ) (hC₀ : 0 < C₀) (hd₀ : 0 < d₀)
    (hsolver : ∀ (w n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
      let G := SimpleGraph.fromRel (fun u v => edge u v = true)
      RobertsonSeymour1986.GM5.TreewidthLE G w →
      ∃ t : ℕ, t + 1 ≤ C₀ * 2 ^ (d₀ * w) * (n + 1) ^ 2 ∧
        let result := planarRAMRun solver (planarRAMInput n w edge weight) t
        solver[result.pc]? = some PlanarRAMInstruction.halt ∧
        (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
        G.IsIndepSet (planarRAMOutput n result : Set (Fin n)) ∧
        ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
          ∑ i ∈ S, weight i ≤ ∑ i ∈ planarRAMOutput n result, weight i) :
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
  obtain ⟨program, C, d, hC, hd, hprog⟩ :=
    WilliamsonShmoys.baker_masked_best_of_runs_ram solver C₀ d₀ hC₀ hd₀ hsolver
  refine ⟨program, C, d, hC, hd, ?_⟩
  intro k hk n edge weight G htw
  have htw' : ∀ j < k, RobertsonSeymour1986.GM5.TreewidthLE
      (SimpleGraph.fromRel (fun u v => G.Adj u v ∧
        bakerLevel G u % k ≠ j ∧ bakerLevel G v % k ≠ j)) (3 * k) :=
    fun j hj => WilliamsonShmoys.treewidth_masked_of_induced G
      (fun v => bakerLevel G v % k ≠ j) (3 * k) (htw j hj)
  obtain ⟨t, ht, hhalt, hbits, hind, hopt⟩ := hprog k hk n edge weight htw'
  refine ⟨t, ht, hhalt, hbits, hind, ?_⟩
  intro j hj S hS hav
  have hS' : (SimpleGraph.fromRel (fun u v => G.Adj u v ∧
      bakerLevel G u % k ≠ j ∧ bakerLevel G v % k ≠ j)).IsIndepSet (S : Set (Fin n)) := by
    intro x hx y hy hxy hadj
    rw [SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with h | h
    · exact hS hx hy hxy h.1
    · exact hS hx hy hxy h.1.symm
  have hsum : ∑ i ∈ S, (if bakerLevel G i % k ≠ j then weight i else 0) = ∑ i ∈ S, weight i :=
    Finset.sum_congr rfl (fun i hi => if_pos (hav i hi))
  have := hopt j hj S hS'
  rw [hsum] at this
  exact this
