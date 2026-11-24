-- Prove2me | solution 1 for WilliamsonShmoys.baker_masked_runs_ram_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:40:04.566288+00:00
-- url     : https://prove2.me/submissions/7f9f9074-0728-4d56-a7d7-e45704b0dc31
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_WilliamsonShmoys_BakerLevelInput
import Theorems.Thm_WilliamsonShmoys_baker_level_ram_clean
import Theorems.Thm_WilliamsonShmoys_baker_masked_runs_from_levels_ram

set_option autoImplicit false
open scoped BigOperators

namespace BakerSeqAux

open WilliamsonShmoys

/-- Shift every jump target of an instruction by `o`. -/
def shiftInstr (o : ℕ) : PlanarRAMInstruction → PlanarRAMInstruction
  | .natBranch l r y n => .natBranch l r (y + o) (n + o)
  | .realBranch l r y n => .realBranch l r (y + o) (n + o)
  | .jump t => .jump (t + o)
  | i => i

/-- Shift the program counter of a state by `o`. -/
def shiftPc (o : ℕ) (s : PlanarRAMState) : PlanarRAMState := { s with pc := s.pc + o }

lemma getElem?_seq (A B : List PlanarRAMInstruction) (p : ℕ) :
    (A ++ B.map (shiftInstr A.length))[p + A.length]? = (B[p]?).map (shiftInstr A.length) := by
  rw [List.getElem?_append_right (by omega), List.getElem?_map]
  congr 2
  omega

/-- One step of the shifted copy simulates one step of the original. -/
lemma step_seq (A B : List PlanarRAMInstruction) (s : PlanarRAMState) :
    planarRAMStep (A ++ B.map (shiftInstr A.length)) (shiftPc A.length s) =
      shiftPc A.length (planarRAMStep B s) := by
  have hget := getElem?_seq A B s.pc
  simp only [shiftPc] at hget ⊢
  unfold planarRAMStep
  rw [hget]
  rcases h : B[s.pc]? with _ | i
  · simp
  · cases i <;> simp [shiftInstr] <;> first | omega | (split_ifs <;> rfl)

lemma run_seq (A B : List PlanarRAMInstruction) (s : PlanarRAMState) (t : ℕ) :
    planarRAMRun (A ++ B.map (shiftInstr A.length)) (shiftPc A.length s) t =
      shiftPc A.length (planarRAMRun B s t) := by
  unfold planarRAMRun
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, step_seq]

/-- A step only reads the instruction at the current program counter. -/
lemma step_congr (P Q : List PlanarRAMInstruction) (s : PlanarRAMState)
    (h : P[s.pc]? = Q[s.pc]?) : planarRAMStep P s = planarRAMStep Q s := by
  unfold planarRAMStep
  rw [h]

/-- While the program counter stays inside `A`, the concatenation behaves like `A`. -/
lemma run_prefix (A B' : List PlanarRAMInstruction) (s : PlanarRAMState) (T : ℕ)
    (hpc : ∀ t < T, (planarRAMRun A s t).pc < A.length) :
    ∀ t ≤ T, planarRAMRun (A ++ B') s t = planarRAMRun A s t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih' := ih (by omega)
    have hlt := hpc t (by omega)
    unfold planarRAMRun at ih' hlt ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih']
    exact step_congr _ _ _ (List.getElem?_append_left hlt)

lemma run_add (P : List PlanarRAMInstruction) (s : PlanarRAMState) (a b : ℕ) :
    planarRAMRun P s (a + b) = planarRAMRun P (planarRAMRun P s a) b := by
  unfold planarRAMRun
  rw [add_comm, Function.iterate_add_apply]

lemma output_eq_of_natMem {n : ℕ} {s s' : PlanarRAMState} (h : s.natMem = s'.natMem) :
    planarRAMOutput n s = planarRAMOutput n s' := by
  unfold planarRAMOutput; rw [h]

end BakerSeqAux

open BakerSeqAux in
theorem solution
    (solver : List WilliamsonShmoys.PlanarRAMInstruction) (C₀ d₀ : ℕ) :
    ∃ (program : List WilliamsonShmoys.PlanarRAMInstruction) (C d : ℕ),
      0 < C ∧ 0 < d ∧
      ∀ (k : ℕ), 0 < k →
      ∀ (n : ℕ) (edge : Fin n → Fin n → Bool) (weight : Fin n → ℝ),
        let G := SimpleGraph.fromRel (fun u v => edge u v = true)
        let maskedEdge : ℕ → Fin n → Fin n → Bool := fun j u v =>
          edge u v && decide (WilliamsonShmoys.bakerLevel G u % k ≠ j) &&
            decide (WilliamsonShmoys.bakerLevel G v % k ≠ j)
        let maskedWeight : ℕ → Fin n → ℝ := fun j i =>
          if WilliamsonShmoys.bakerLevel G i % k ≠ j then weight i else 0
        let inst : ℕ → WilliamsonShmoys.PlanarRAMState := fun j =>
          WilliamsonShmoys.planarRAMInput n (3 * k) (maskedEdge j) (maskedWeight j)
        (∀ j < k, ∃ t : ℕ, t + 1 ≤ C₀ * 2 ^ (d₀ * (3 * k)) * (n + 1) ^ 2 ∧
          solver[(WilliamsonShmoys.planarRAMRun solver (inst j) t).pc]? =
            some WilliamsonShmoys.PlanarRAMInstruction.halt) →
        ∃ t : ℕ, t + 1 ≤ C * 2 ^ (d * k) * (n + 1) ^ 2 ∧
          let result := WilliamsonShmoys.planarRAMRun program
            (WilliamsonShmoys.planarRAMInput n k edge weight) t
          program[result.pc]? = some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
          (∀ i : Fin n, result.natMem (2 + n * n + i.val) ≤ 1) ∧
          (∃ j₀ < k, ∃ t₀ : ℕ,
            solver[(WilliamsonShmoys.planarRAMRun solver (inst j₀) t₀).pc]? =
              some WilliamsonShmoys.PlanarRAMInstruction.halt ∧
            WilliamsonShmoys.planarRAMOutput n result =
              (WilliamsonShmoys.planarRAMOutput n
                (WilliamsonShmoys.planarRAMRun solver (inst j₀) t₀)).filter
                  (fun i => WilliamsonShmoys.bakerLevel G i % k ≠ j₀)) ∧
          ∀ j < k, ∀ t' : ℕ,
            solver[(WilliamsonShmoys.planarRAMRun solver (inst j) t').pc]? =
              some WilliamsonShmoys.PlanarRAMInstruction.halt →
            ∑ i ∈ (WilliamsonShmoys.planarRAMOutput n
                (WilliamsonShmoys.planarRAMRun solver (inst j) t')).filter
                  (fun i => WilliamsonShmoys.bakerLevel G i % k ≠ j), weight i ≤
              ∑ i ∈ WilliamsonShmoys.planarRAMOutput n result, weight i := by
  obtain ⟨A, C₁, hC₁, hA⟩ := WilliamsonShmoys.baker_level_ram_clean
  obtain ⟨B, C₂, d, hC₂, hd, hB⟩ :=
    WilliamsonShmoys.baker_masked_runs_from_levels_ram solver C₀ d₀
  refine ⟨A ++ B.map (shiftInstr A.length), C₁ + C₂, d, by omega, hd, ?_⟩
  intro k hk n edge weight G maskedEdge maskedWeight inst hhalt
  obtain ⟨T, hT, hpc, hTstate⟩ := hA k hk n edge weight
  obtain ⟨t, ht, hBhalt, hbits, hsel, hdom⟩ := hB k hk n edge weight hhalt
  -- the state of the concatenated program after `T + t` steps
  have hstate : WilliamsonShmoys.planarRAMRun (A ++ B.map (shiftInstr A.length))
      (WilliamsonShmoys.planarRAMInput n k edge weight) (T + t) =
      shiftPc A.length (WilliamsonShmoys.planarRAMRun B
        (WilliamsonShmoys.bakerLevelInput n k edge weight) t) := by
    rw [run_add, run_prefix A _ _ T hpc T le_rfl, hTstate]
    have : ({ WilliamsonShmoys.bakerLevelInput n k edge weight with pc := A.length } :
        WilliamsonShmoys.PlanarRAMState) =
        shiftPc A.length (WilliamsonShmoys.bakerLevelInput n k edge weight) := by
      simp [shiftPc, WilliamsonShmoys.bakerLevelInput, WilliamsonShmoys.planarRAMInput]
    rw [this, run_seq]
  refine ⟨T + t, ?_, ?_⟩
  · have h2 : 1 ≤ 2 ^ (d * k) := Nat.one_le_two_pow
    have hsq : 0 ≤ (n + 1) ^ 2 := Nat.zero_le _
    calc T + t + 1 ≤ C₁ * (n + 1) ^ 2 + C₂ * 2 ^ (d * k) * (n + 1) ^ 2 := by omega
      _ ≤ C₁ * 2 ^ (d * k) * (n + 1) ^ 2 + C₂ * 2 ^ (d * k) * (n + 1) ^ 2 := by
          gcongr
          exact Nat.le_mul_of_pos_right _ (by positivity)
      _ = (C₁ + C₂) * 2 ^ (d * k) * (n + 1) ^ 2 := by ring
  · intro result
    have hres : result = shiftPc A.length (WilliamsonShmoys.planarRAMRun B
        (WilliamsonShmoys.bakerLevelInput n k edge weight) t) := hstate
    have hnat : result.natMem = (WilliamsonShmoys.planarRAMRun B
        (WilliamsonShmoys.bakerLevelInput n k edge weight) t).natMem := by
      rw [hres]; rfl
    have hout := output_eq_of_natMem (n := n) hnat
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hres]
      simp only [shiftPc]
      rw [getElem?_seq, hBhalt]
      rfl
    · intro i; rw [hnat]; exact hbits i
    · obtain ⟨j₀, hj₀, t₀, ht₀, heq⟩ := hsel
      exact ⟨j₀, hj₀, t₀, ht₀, by rw [hout]; exact heq⟩
    · intro j hj t' ht'
      rw [hout]; exact hdom j hj t' ht'
