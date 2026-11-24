-- Prove2me | solution 1 for WilliamsonShmoys.baker_masked_best_of_runs_ram
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:22:00.125026+00:00
-- url     : https://prove2.me/submissions/219e3a97-09f9-48c0-8ed6-7cef1db70b36
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Theorems.Thm_WilliamsonShmoys_baker_masked_runs_ram_core

set_option autoImplicit false
open scoped BigOperators

namespace BakerReductionAux

open WilliamsonShmoys

/-- A halted RAM state is a fixed point of the step function. -/
lemma step_of_halt (program : List PlanarRAMInstruction) (s : PlanarRAMState)
    (h : program[s.pc]? = some PlanarRAMInstruction.halt) :
    planarRAMStep program s = s := by
  unfold planarRAMStep
  simp only [h]

lemma iterate_of_halt (program : List PlanarRAMInstruction) (s : PlanarRAMState)
    (h : program[s.pc]? = some PlanarRAMInstruction.halt) (m : ℕ) :
    (planarRAMStep program)^[m] s = s := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, step_of_halt program s h, ih]

/-- Two halting times of the same run reach the same state. -/
lemma run_eq_of_halt (program : List PlanarRAMInstruction) (s : PlanarRAMState) (t₁ t₂ : ℕ)
    (h₁ : program[(planarRAMRun program s t₁).pc]? = some PlanarRAMInstruction.halt)
    (h₂ : program[(planarRAMRun program s t₂).pc]? = some PlanarRAMInstruction.halt) :
    planarRAMRun program s t₁ = planarRAMRun program s t₂ := by
  have key : ∀ a b : ℕ, a ≤ b →
      program[(planarRAMRun program s a).pc]? = some PlanarRAMInstruction.halt →
      planarRAMRun program s b = planarRAMRun program s a := by
    intro a b hab ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hab
    unfold planarRAMRun at ha ⊢
    rw [add_comm, Function.iterate_add_apply]
    exact iterate_of_halt program _ ha m
  rcases le_total t₁ t₂ with h | h
  · exact (key t₁ t₂ h h₁).symm
  · exact key t₂ t₁ h h₂

end BakerReductionAux

open BakerReductionAux in
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
  obtain ⟨program, C, d, hC, hd, hcore⟩ :=
    WilliamsonShmoys.baker_masked_runs_ram_core solver C₀ d₀
  refine ⟨program, C, d, hC, hd, ?_⟩
  intro k hk n edge weight G htw
  -- the masked graph described by the masked adjacency table
  set Gm : ℕ → SimpleGraph (Fin n) := fun j =>
    SimpleGraph.fromRel (fun u v => G.Adj u v ∧
      WilliamsonShmoys.bakerLevel G u % k ≠ j ∧ WilliamsonShmoys.bakerLevel G v % k ≠ j)
    with hGm
  set mEdge : ℕ → Fin n → Fin n → Bool := fun j u v =>
    edge u v && decide (WilliamsonShmoys.bakerLevel G u % k ≠ j) &&
      decide (WilliamsonShmoys.bakerLevel G v % k ≠ j) with hmEdge
  set mWeight : ℕ → Fin n → ℝ := fun j i =>
    if WilliamsonShmoys.bakerLevel G i % k ≠ j then weight i else 0 with hmWeight
  have hgraph : ∀ j, SimpleGraph.fromRel (fun u v => mEdge j u v = true) = Gm j := by
    intro j
    ext u v
    simp only [hGm, hmEdge, G, SimpleGraph.fromRel_adj, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨huv, h | h⟩
      · exact ⟨huv, Or.inl ⟨⟨huv, Or.inl h.1.1⟩, h.1.2, h.2⟩⟩
      · exact ⟨huv, Or.inl ⟨⟨huv, Or.inr h.1.1⟩, h.2, h.1.2⟩⟩
    · rintro ⟨huv, ⟨⟨-, he⟩, hu, hv⟩ | ⟨⟨-, he⟩, hv, hu⟩⟩
      · rcases he with he | he
        · exact ⟨huv, Or.inl ⟨⟨he, hu⟩, hv⟩⟩
        · exact ⟨huv, Or.inr ⟨⟨he, hv⟩, hu⟩⟩
      · rcases he with he | he
        · exact ⟨huv, Or.inr ⟨⟨he, hv⟩, hu⟩⟩
        · exact ⟨huv, Or.inl ⟨⟨he, hu⟩, hv⟩⟩
  -- the solver's guarantee on each masked instance
  have hrun : ∀ j < k, ∃ t : ℕ, t + 1 ≤ C₀ * 2 ^ (d₀ * (3 * k)) * (n + 1) ^ 2 ∧
      solver[(WilliamsonShmoys.planarRAMRun solver
        (WilliamsonShmoys.planarRAMInput n (3 * k) (mEdge j) (mWeight j)) t).pc]? =
          some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
      (Gm j).IsIndepSet (WilliamsonShmoys.planarRAMOutput n (WilliamsonShmoys.planarRAMRun solver
        (WilliamsonShmoys.planarRAMInput n (3 * k) (mEdge j) (mWeight j)) t) : Set (Fin n)) ∧
      ∀ S : Finset (Fin n), (Gm j).IsIndepSet (S : Set (Fin n)) →
        ∑ i ∈ S, mWeight j i ≤ ∑ i ∈ WilliamsonShmoys.planarRAMOutput n
          (WilliamsonShmoys.planarRAMRun solver
            (WilliamsonShmoys.planarRAMInput n (3 * k) (mEdge j) (mWeight j)) t), mWeight j i := by
    intro j hj
    have htw' : RobertsonSeymour1986.GM5.TreewidthLE
        (SimpleGraph.fromRel (fun u v => mEdge j u v = true)) (3 * k) := by
      rw [hgraph j]; exact htw j hj
    obtain ⟨t, ht, hhalt, -, hind, hopt⟩ := hsolver (3 * k) n (mEdge j) (mWeight j) htw'
    refine ⟨t, ht, hhalt, ?_, ?_⟩
    · rw [← hgraph j]; exact hind
    · intro S hS
      exact hopt S (by rw [hgraph j]; exact hS)
  obtain ⟨t, ht, hhalt, hbits, ⟨j₀, hj₀, t₀, ht₀, hout⟩, hdom⟩ :=
    hcore k hk n edge weight (fun j hj => by
      obtain ⟨t, ht, hh, -⟩ := hrun j hj
      exact ⟨t, ht, hh⟩)
  refine ⟨t, ht, hhalt, hbits, ?_, ?_⟩
  · -- independence of the selected, filtered solver output
    obtain ⟨t₁, -, ht₁, hind, -⟩ := hrun j₀ hj₀
    rw [run_eq_of_halt solver _ t₀ t₁ ht₀ ht₁] at hout
    rw [hout]
    intro u hu v hv huv hadj
    simp only [Finset.coe_filter] at hu hv
    exact hind hu.1 hv.1 huv (by
      rw [hGm, SimpleGraph.fromRel_adj]
      exact ⟨huv, Or.inl ⟨hadj, hu.2, hv.2⟩⟩)
  · -- domination of every masked independent set
    intro j hj S hS
    obtain ⟨tj, -, htj, -, hopt⟩ := hrun j hj
    have h1 := hopt S hS
    have h2 := hdom j hj tj htj
    rw [Finset.sum_filter] at h2
    exact le_trans h1 h2
