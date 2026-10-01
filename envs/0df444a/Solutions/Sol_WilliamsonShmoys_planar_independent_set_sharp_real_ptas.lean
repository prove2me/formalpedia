-- Prove2me | solution 1 for WilliamsonShmoys.planar_independent_set_sharp_real_ptas
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-30T13:53:06.037647+00:00
-- url     : https://prove2.me/submissions/b893c352-2543-4040-8178-e418838a4c91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Theorems.Thm_WilliamsonShmoys_shifting_bound
import Theorems.Thm_WilliamsonShmoys_planar_bfs_band_treewidth
import Theorems.Thm_WilliamsonShmoys_band_treewidth_ram_solver

set_option autoImplicit false
open scoped BigOperators

open WilliamsonShmoys in
theorem solution :
    ∃ (program : List PlanarRAMInstruction) (C d : ℕ),
      0 < C ∧ 0 < d ∧
      ∀ (ε : ℝ), 0 < ε →
      ∀ (n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        let G := SimpleGraph.fromRel (fun u v => edge u v = true)
        let k := max 1 ⌈ε⁻¹⌉₊
        HasPlanarDrawing G → (∀ i, 0 ≤ weight i) →
        ∃ t : ℕ, t + 1 ≤ C * 2 ^ (d * k) * (n + 1) ^ 2 ∧
          let result := planarRAMRun program (planarRAMInput n k edge weight) t
          program[result.pc]? = some PlanarRAMInstruction.halt ∧
          (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
          G.IsIndepSet (planarRAMOutput n result : Set (Fin n)) ∧
          ∀ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) →
            (1 - ε) * (∑ i ∈ S, weight i) ≤
              ∑ i ∈ planarRAMOutput n result, weight i := by
  obtain ⟨program, C, d, hC, hd, hsolve⟩ := band_treewidth_ram_solver
  refine ⟨program, C, d, hC, hd, ?_⟩
  intro ε hε n edge weight G k hplanar hw
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hband : ∀ j < k, RobertsonSeymour1986.GM5.TreewidthLE
      (G.induce {v : Fin n | bakerLevel G v % k ≠ j}) (3 * k) :=
    fun j hj => planar_bfs_band_treewidth G k j hk hj hplanar
  obtain ⟨t, ht, hhalt, hbits, hind, hopt⟩ := hsolve k hk n edge weight hband
  refine ⟨t, ht, hhalt, hbits, hind, ?_⟩
  intro S hS
  have hshift := shifting_bound G weight (bakerLevel G) k hk _ hopt S hS
  have hSnn : 0 ≤ ∑ i ∈ S, weight i := Finset.sum_nonneg fun i _ => hw i
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hinv : (1 : ℝ) / k ≤ ε := by
    have h1 : ε⁻¹ ≤ (k : ℝ) :=
      (Nat.le_ceil ε⁻¹).trans (by exact_mod_cast le_max_right 1 ⌈ε⁻¹⌉₊)
    rw [div_le_iff₀ hkpos]
    have := mul_le_mul_of_nonneg_left h1 hε.le
    rwa [mul_inv_cancel₀ hε.ne'] at this
  calc (1 - ε) * ∑ i ∈ S, weight i ≤ (1 - 1 / (k : ℝ)) * ∑ i ∈ S, weight i :=
        mul_le_mul_of_nonneg_right (by linarith) hSnn
    _ ≤ _ := hshift
