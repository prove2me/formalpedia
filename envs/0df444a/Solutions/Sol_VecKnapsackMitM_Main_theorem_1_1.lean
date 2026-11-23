-- Prove2me | solution 1 for VecKnapsackMitM.Main.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:58:24.124265+00:00
-- url     : https://prove2.me/submissions/33170a47-e9cf-4284-a1d3-c942aecb9667
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine
import Theorems.Thm_VecKnapsackMitM_Main_lemma_4_6
import Theorems.Thm_VecKnapsackMitM_Main_lemma_4_7

namespace Aux11

open VecKnapsackMitM.Main MatMulTimeLP

def shiftInstr (off : ℕ) : Instr → Instr
  | Instr.rblt i j l => Instr.rblt i j (off + l)
  | Instr.nblt i j l => Instr.nblt i j (off + l)
  | ins => ins

def shiftProg (off : ℕ) (Q : Program) : Program := Q.map (shiftInstr off)

lemma shiftProg_admissible (off : ℕ) {Q : Program} (hQ : VecBalPoly.Admissible Q) :
    VecBalPoly.Admissible (shiftProg off Q) := by
  intro ins hins
  rw [shiftProg, List.mem_map] at hins
  obtain ⟨ins0, hins0, rfl⟩ := hins
  have h0 := hQ ins0 hins0
  cases ins0 <;> simp [shiftInstr, VecBalPoly.InstrAdmissible] at h0 ⊢
  exact h0

lemma step_zeroTape_indep (P : Program) (t₁ t₂ : ℕ) (s : State) :
    step P zeroTape t₁ s = step P zeroTape t₂ s := by
  unfold step
  cases P[s.pc]? with
  | none => rfl
  | some ins =>
    cases ins <;> rfl

lemma run_add (P : Program) (s₀ : State) (a : ℕ) :
    ∀ b : ℕ, run P s₀ (a + b) = run P (run P s₀ a) b
  | 0 => rfl
  | b + 1 => by
    change step P zeroTape (a + b) (run P s₀ (a + b)) =
      step P zeroTape b (run P (run P s₀ a) b)
    rw [run_add P s₀ a b]
    exact step_zeroTape_indep P (a + b) b _

def liftState (off : ℕ) (s : State) : State := ⟨off + s.pc, s.R, s.N⟩

lemma step_append_shift (W Q : Program) (s : State) :
    step (W ++ shiftProg W.length Q) zeroTape 0 (liftState W.length s) =
      liftState W.length (step Q zeroTape 0 s) := by
  have hget : (W ++ shiftProg W.length Q)[W.length + s.pc]? =
      (Q[s.pc]?).map (shiftInstr W.length) := by
    rw [List.getElem?_append_right (Nat.le_add_right W.length s.pc),
      Nat.add_sub_cancel_left, shiftProg, List.getElem?_map]
  unfold step liftState
  dsimp only []
  rw [hget]
  cases Q[s.pc]? with
  | none => rfl
  | some ins =>
    cases ins with
    | rblt i j l =>
      dsimp [shiftInstr]
      split_ifs <;> simp [Nat.add_assoc]
    | nblt i j l =>
      dsimp [shiftInstr]
      split_ifs <;> simp [Nat.add_assoc]
    | halt => rfl
    | rconst _ _ => simp [shiftInstr, Nat.add_assoc]
    | radd _ _ _ => simp [shiftInstr, Nat.add_assoc]
    | rsub _ _ _ => simp [shiftInstr, Nat.add_assoc]
    | rmul _ _ _ => simp [shiftInstr, Nat.add_assoc]
    | rdiv _ _ _ => simp [shiftInstr, Nat.add_assoc]
    | rsqrt _ _ => simp [shiftInstr, Nat.add_assoc]
    | rload _ _ => simp [shiftInstr, Nat.add_assoc]
    | rstore _ _ => simp [shiftInstr, Nat.add_assoc]
    | nconst _ _ => simp [shiftInstr, Nat.add_assoc]
    | nadd _ _ _ => simp [shiftInstr, Nat.add_assoc]
    | nsub _ _ _ => simp [shiftInstr, Nat.add_assoc]
    | nload _ _ => simp [shiftInstr, Nat.add_assoc]
    | nstore _ _ => simp [shiftInstr, Nat.add_assoc]
    | gauss _ => simp [shiftInstr, Nat.add_assoc]
    | unif _ => simp [shiftInstr, Nat.add_assoc]

lemma run_append_shift (W Q : Program) (s₀ : State) :
    ∀ t : ℕ, run (W ++ shiftProg W.length Q) (liftState W.length s₀) t =
      liftState W.length (run Q s₀ t)
  | 0 => rfl
  | t + 1 => by
    change step (W ++ shiftProg W.length Q) zeroTape t
        (run (W ++ shiftProg W.length Q) (liftState W.length s₀) t) =
      liftState W.length (step Q zeroTape t (run Q s₀ t))
    rw [run_append_shift W Q s₀ t,
      step_zeroTape_indep _ t 0 _,
      step_zeroTape_indep Q t 0 _,
      step_append_shift W Q _]

lemma isHalted_append_shift (W Q : Program) (s : State) (h : IsHalted Q s) :
    IsHalted (W ++ shiftProg W.length Q) (liftState W.length s) := by
  unfold IsHalted liftState at *
  dsimp only []
  rw [List.getElem?_append_right (Nat.le_add_right W.length s.pc),
    Nat.add_sub_cancel_left, shiftProg, List.getElem?_map]
  rcases h with hnone | hhalt
  · rw [hnone]; exact Or.inl rfl
  · rw [hhalt]; exact Or.inr rfl

/-- The 33-instruction reversible wrapper program setting `R[0] := min(R[0], (d - 1) / d)`
using only `R[0]`, read-only `R[1] = ρ > 0`, and scratch index cells `N[2], N[3], N[4]`. -/
def wrapProg : Program :=
  [ -- 0..5: setup N[2]=1, N[3]=d-1, and R[0] = ρ / (1 - ε)
    Instr.nconst 2 1,       -- 0
    Instr.nsub 3 0 2,       -- 1
    Instr.rmul 0 0 1,       -- 2
    Instr.rsub 0 1 0,       -- 3
    Instr.rdiv 0 1 0,       -- 4
    Instr.rmul 0 0 1,       -- 5
    -- 6..10: Loop A (subtract ρ (d - 1) times)
    Instr.nblt 4 3 8,       -- 6
    Instr.nblt 4 2 11,      -- 7
    Instr.rsub 0 0 1,       -- 8
    Instr.nsub 3 3 2,       -- 9
    Instr.nblt 4 2 6,       -- 10
    -- 11: test ρ < R[0]  (↔ (d - 1) / d < ε)
    Instr.rblt 1 0 21,      -- 11
    -- 12..20: False branch (ε ≤ (d - 1) / d): invert back to (1 - ε) * ρ, jump to 30
    Instr.nsub 3 0 2,       -- 12
    Instr.nblt 4 3 15,      -- 13
    Instr.nblt 4 2 18,      -- 14
    Instr.radd 0 0 1,       -- 15
    Instr.nsub 3 3 2,       -- 16
    Instr.nblt 4 2 13,      -- 17
    Instr.rdiv 0 1 0,       -- 18
    Instr.rmul 0 0 1,       -- 19
    Instr.nblt 4 2 30,      -- 20
    -- 21..29: True branch ((d - 1) / d < ε): compute ρ / d, fall through to 30
    Instr.rconst 0 0,       -- 21
    Instr.nadd 3 0 4,       -- 22
    Instr.nblt 4 3 25,      -- 23
    Instr.nblt 4 2 28,      -- 24
    Instr.radd 0 0 1,       -- 25
    Instr.nsub 3 3 2,       -- 26
    Instr.nblt 4 2 23,      -- 27
    Instr.rdiv 0 1 0,       -- 28
    Instr.rmul 0 0 1,       -- 29
    -- 30..32: Shared tail: R[0] := (ρ - R[0]) / ρ, zero N[2]
    Instr.rsub 0 1 0,       -- 30
    Instr.rdiv 0 0 1,       -- 31
    Instr.nconst 2 0        -- 32
  ]

lemma wrapProg_length : wrapProg.length = 33 := rfl

lemma wrapProg_admissible : VecBalPoly.Admissible wrapProg := by
  intro ins hins
  simp only [wrapProg, List.mem_cons, List.not_mem_nil, or_false] at hins
  rcases hins with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [VecBalPoly.InstrAdmissible]
  exact ⟨0, by norm_num⟩

lemma run_one (P : Program) (s : State) : run P s 1 = step P zeroTape 0 s := rfl

lemma get_wrap (Q : Program) (k : ℕ) (hk : k < 33) :
    (wrapProg ++ Q)[k]? = wrapProg[k]? :=
  List.getElem?_append_left (by simpa [wrapProg_length] using hk)

/-- Execution of Loop A (pc 6..10) for `m` iterations. -/
lemma run_loopA (Q : Program) (R0 : ℕ → ℝ) (N0 : ℕ → ℕ) (ρ : ℝ)
    (hR1 : R0 1 = ρ) (hN2 : N0 2 = 1) (hN4 : N0 4 = 0) :
    ∀ (m : ℕ) (val : ℝ),
      run (wrapProg ++ Q) ⟨6, Function.update R0 0 val, Function.update N0 3 m⟩ (4 * m + 2) =
        ⟨11, Function.update R0 0 (val - (m : ℝ) * ρ), Function.update N0 3 0⟩
  | 0, val => by
    have h1 : run (wrapProg ++ Q) ⟨6, Function.update R0 0 val, Function.update N0 3 0⟩ 1 =
        ⟨7, Function.update R0 0 val, Function.update N0 3 0⟩ := by
      have hp : (wrapProg ++ Q)[6]? = some (Instr.nblt 4 3 8) := by
        rw [get_wrap Q 6 (by omega)]; rfl
      rw [run_one]; unfold step; dsimp only []; rw [hp]
      simp [Function.update_of_ne, hN4]
    have h2 : run (wrapProg ++ Q) ⟨7, Function.update R0 0 val, Function.update N0 3 0⟩ 1 =
        ⟨11, Function.update R0 0 val, Function.update N0 3 0⟩ := by
      have hp : (wrapProg ++ Q)[7]? = some (Instr.nblt 4 2 11) := by
        rw [get_wrap Q 7 (by omega)]; rfl
      rw [run_one]; unfold step; dsimp only []; rw [hp]
      simp [Function.update_of_ne, hN4, hN2]
    have htotal : (4 * 0 + 2 : ℕ) = 1 + 1 := rfl
    rw [htotal, run_add, h1, h2]
    simp
  | m + 1, val => by
    let P := wrapProg ++ Q
    have s1 : run P ⟨6, Function.update R0 0 val, Function.update N0 3 (m + 1)⟩ 1 =
        ⟨8, Function.update R0 0 val, Function.update N0 3 (m + 1)⟩ := by
      have hp : P[6]? = some (Instr.nblt 4 3 8) := by rw [get_wrap Q 6 (by omega)]; rfl
      rw [run_one]; unfold step; dsimp only []; rw [hp]
      simp [Function.update_of_ne, hN4]
    have s2 : run P ⟨8, Function.update R0 0 val, Function.update N0 3 (m + 1)⟩ 1 =
        ⟨9, Function.update R0 0 (val - ρ), Function.update N0 3 (m + 1)⟩ := by
      have hp : P[8]? = some (Instr.rsub 0 0 1) := by rw [get_wrap Q 8 (by omega)]; rfl
      rw [run_one]; unfold step; dsimp only []; rw [hp]
      simp [hR1]
    have s3 : run P ⟨9, Function.update R0 0 (val - ρ), Function.update N0 3 (m + 1)⟩ 1 =
        ⟨10, Function.update R0 0 (val - ρ), Function.update N0 3 m⟩ := by
      have hp : P[9]? = some (Instr.nsub 3 3 2) := by rw [get_wrap Q 9 (by omega)]; rfl
      rw [run_one]; unfold step; dsimp only []; rw [hp]
      simp [hN2]
    have s4 : run P ⟨10, Function.update R0 0 (val - ρ), Function.update N0 3 m⟩ 1 =
        ⟨6, Function.update R0 0 (val - ρ), Function.update N0 3 m⟩ := by
      have hp : P[10]? = some (Instr.nblt 4 2 6) := by rw [get_wrap Q 10 (by omega)]; rfl
      rw [run_one]; unfold step; dsimp only []; rw [hp]
      simp [hN4, hN2]
    have hsplit : 4 * (m + 1) + 2 = 1 + (1 + (1 + (1 + (4 * m + 2)))) := by omega
    rw [hsplit, run_add, s1, run_add, s2, run_add, s3, run_add, s4,
      run_loopA Q R0 N0 ρ hR1 hN2 hN4 m (val - ρ)]
    congr 2
    push_cast
    ring_nf

/-- Execution of Loop B (pc 13..17, exit 18) or Loop C (pc 23..27, exit 28). -/
lemma run_addLoop (Q : Program) (base exit : ℕ)
    (hp0 : (wrapProg ++ Q)[base]? = some (Instr.nblt 4 3 (base + 2)))
    (hp1 : (wrapProg ++ Q)[base + 1]? = some (Instr.nblt 4 2 exit))
    (hp2 : (wrapProg ++ Q)[base + 2]? = some (Instr.radd 0 0 1))
    (hp3 : (wrapProg ++ Q)[base + 3]? = some (Instr.nsub 3 3 2))
    (hp4 : (wrapProg ++ Q)[base + 4]? = some (Instr.nblt 4 2 base))
    (R0 : ℕ → ℝ) (N0 : ℕ → ℕ) (ρ : ℝ)
    (hR1 : R0 1 = ρ) (hN2 : N0 2 = 1) (hN4 : N0 4 = 0) :
    ∀ (m : ℕ) (val : ℝ),
      run (wrapProg ++ Q) ⟨base, Function.update R0 0 val, Function.update N0 3 m⟩ (4 * m + 2) =
        ⟨exit, Function.update R0 0 (val + (m : ℝ) * ρ), Function.update N0 3 0⟩
  | 0, val => by
    let P := wrapProg ++ Q
    have s1 : run P ⟨base, Function.update R0 0 val, Function.update N0 3 0⟩ 1 =
        ⟨base + 1, Function.update R0 0 val, Function.update N0 3 0⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [hp0]; simp [hN4]
    have s2 : run P ⟨base + 1, Function.update R0 0 val, Function.update N0 3 0⟩ 1 =
        ⟨exit, Function.update R0 0 val, Function.update N0 3 0⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [hp1]; simp [hN4, hN2]
    have htotal : (4 * 0 + 2 : ℕ) = 1 + 1 := rfl
    rw [htotal, run_add, s1, s2]
    simp
  | m + 1, val => by
    let P := wrapProg ++ Q
    have s1 : run P ⟨base, Function.update R0 0 val, Function.update N0 3 (m + 1)⟩ 1 =
        ⟨base + 2, Function.update R0 0 val, Function.update N0 3 (m + 1)⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [hp0]; simp [hN4]
    have s2 : run P ⟨base + 2, Function.update R0 0 val, Function.update N0 3 (m + 1)⟩ 1 =
        ⟨base + 3, Function.update R0 0 (val + ρ), Function.update N0 3 (m + 1)⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [hp2]; simp [hR1]
    have s3 : run P ⟨base + 3, Function.update R0 0 (val + ρ), Function.update N0 3 (m + 1)⟩ 1 =
        ⟨base + 4, Function.update R0 0 (val + ρ), Function.update N0 3 m⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [hp3]; simp [hN2]
    have s4 : run P ⟨base + 4, Function.update R0 0 (val + ρ), Function.update N0 3 m⟩ 1 =
        ⟨base, Function.update R0 0 (val + ρ), Function.update N0 3 m⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [hp4]; simp [hN4, hN2]
    have hsplit : 4 * (m + 1) + 2 = 1 + (1 + (1 + (1 + (4 * m + 2)))) := by omega
    rw [hsplit, run_add, s1, run_add, s2, run_add, s3, run_add, s4,
      run_addLoop Q base exit hp0 hp1 hp2 hp3 hp4 R0 N0 ρ hR1 hN2 hN4 m (val + ρ)]
    congr 2
    push_cast
    ring_nf

/-- Full execution of `wrapProg` on `knapsackInput inst ε ρ`. -/
lemma run_wrapProg {d n : ℕ} (hd : 2 ≤ d) (inst : Instance d n)
    {ε ρ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hρ0 : 0 < ρ) (Q : Program) :
    let ε' := min ε (((d : ℝ) - 1) / d)
    ∃ tw : ℕ, tw ≤ 8 * d + 16 ∧
      run (wrapProg ++ shiftProg wrapProg.length Q) (knapsackInput inst ε ρ) tw =
        liftState wrapProg.length (knapsackInput inst ε' ρ) := by
  intro ε'
  let P := wrapProg ++ shiftProg wrapProg.length Q
  let Qs := shiftProg wrapProg.length Q
  let s₀ := knapsackInput inst ε ρ
  have hs₀_pc : s₀.pc = 0 := rfl
  have hs₀_R0 : s₀.R 0 = ε := rfl
  have hs₀_R1 : s₀.R 1 = ρ := rfl
  have hs₀_N0 : s₀.N 0 = d := rfl
  have hs₀_N2 : s₀.N 2 = 0 := rfl
  have hs₀_N3 : s₀.N 3 = 0 := rfl
  have hs₀_N4 : s₀.N 4 = 0 := rfl
  let N1 := Function.update s₀.N 2 1
  have hN1_0 : N1 0 = d := by simp [N1, hs₀_N0]
  have hN1_2 : N1 2 = 1 := by simp [N1]
  have hN1_4 : N1 4 = 0 := by simp [N1, hs₀_N4]
  -- Steps 0..5 (6 instructions)
  have h0_6 : run P s₀ 6 =
      ⟨6, Function.update s₀.R 0 (ρ / (1 - ε)), Function.update N1 3 (d - 1)⟩ := by
    have p0 : P[0]? = some (Instr.nconst 2 1) := by rw [get_wrap Qs 0 (by omega)]; rfl
    have p1 : P[1]? = some (Instr.nsub 3 0 2) := by rw [get_wrap Qs 1 (by omega)]; rfl
    have p2 : P[2]? = some (Instr.rmul 0 0 1) := by rw [get_wrap Qs 2 (by omega)]; rfl
    have p3 : P[3]? = some (Instr.rsub 0 1 0) := by rw [get_wrap Qs 3 (by omega)]; rfl
    have p4 : P[4]? = some (Instr.rdiv 0 1 0) := by rw [get_wrap Qs 4 (by omega)]; rfl
    have p5 : P[5]? = some (Instr.rmul 0 0 1) := by rw [get_wrap Qs 5 (by omega)]; rfl
    have st0 : run P s₀ 1 = ⟨1, s₀.R, N1⟩ := by
      rw [run_one]; unfold step; rw [hs₀_pc, p0]
    have st1 : run P ⟨1, s₀.R, N1⟩ 1 = ⟨2, s₀.R, Function.update N1 3 (d - 1)⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [p1]; simp [hN1_0, hN1_2]
    have st2 : run P ⟨2, s₀.R, Function.update N1 3 (d - 1)⟩ 1 =
        ⟨3, Function.update s₀.R 0 (ε * ρ), Function.update N1 3 (d - 1)⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [p2]; simp [hs₀_R0, hs₀_R1]
    have st3 : run P ⟨3, Function.update s₀.R 0 (ε * ρ), Function.update N1 3 (d - 1)⟩ 1 =
        ⟨4, Function.update s₀.R 0 (ρ - ε * ρ), Function.update N1 3 (d - 1)⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [p3]; simp [hs₀_R1]
    have st4 : run P ⟨4, Function.update s₀.R 0 (ρ - ε * ρ), Function.update N1 3 (d - 1)⟩ 1 =
        ⟨5, Function.update s₀.R 0 (ρ / (ρ - ε * ρ)), Function.update N1 3 (d - 1)⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [p4]; simp [hs₀_R1]
    have st5 : run P ⟨5, Function.update s₀.R 0 (ρ / (ρ - ε * ρ)), Function.update N1 3 (d - 1)⟩ 1 =
        ⟨6, Function.update s₀.R 0 (ρ / (1 - ε)), Function.update N1 3 (d - 1)⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [p5]; simp only [Function.update_self,
        Function.update_of_ne (by omega : (1 : ℕ) ≠ 0), hs₀_R1, Function.update_idem]
      congr 2
      have h1e : 1 - ε ≠ 0 := by linarith
      field_simp [hρ0.ne', h1e]
    have h6 : (6 : ℕ) = 1 + (1 + (1 + (1 + (1 + 1)))) := rfl
    rw [h6, run_add, st0, run_add, st1, run_add, st2, run_add, st3, run_add, st4, st5]
  -- Loop A: 4*(d-1)+2 steps to pc = 11
  let vA : ℝ := ρ / (1 - ε) - ((d - 1 : ℕ) : ℝ) * ρ
  have h_to11 : run P s₀ (6 + (4 * (d - 1) + 2)) =
      ⟨11, Function.update s₀.R 0 vA, Function.update N1 3 0⟩ := by
    rw [run_add, h0_6]
    exact run_loopA Qs s₀.R N1 ρ hs₀_R1 hN1_2 hN1_4 (d - 1) (ρ / (1 - ε))
  -- Equivalence ρ < vA ↔ (d - 1) / d < ε
  have hcond_iff : ρ < vA ↔ ((d : ℝ) - 1) / d < ε := by
    have hd_pos : (0 : ℝ) < d := by positivity
    have h1e_pos : 0 < 1 - ε := by linarith
    have hd1_cast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    dsimp [vA]
    rw [hd1_cast]
    constructor
    · intro hlt
      have h1 : (d : ℝ) * ρ < ρ / (1 - ε) := by linarith
      have h2 : (d : ℝ) * (1 - ε) * ρ < ρ := by
        have := (lt_div_iff₀ h1e_pos).mp h1
        linarith
      have h3 : (d : ℝ) * (1 - ε) < 1 := by nlinarith
      rw [div_lt_iff₀ hd_pos]
      linarith
    · intro hlt
      have h1 : (d : ℝ) - 1 < ε * d := (div_lt_iff₀ hd_pos).mp hlt
      have h2 : (d : ℝ) * (1 - ε) < 1 := by linarith
      have h3 : (d : ℝ) * ρ * (1 - ε) < ρ := by nlinarith
      have h4 : (d : ℝ) * ρ < ρ / (1 - ε) := (lt_div_iff₀ h1e_pos).mpr (by linarith)
      linarith
  -- Helper matching final R and N with knapsackInput inst ε' ρ
  have hN_clean : Function.update (Function.update N1 3 0) 2 0 = (knapsackInput inst ε' ρ).N := by
    ext m
    by_cases hm3 : m = 3
    · subst hm3; simp [N1, knapsackInput, initState2, ShadowBootstrap.initState2]
    · by_cases hm2 : m = 2
      · subst hm2; simp [N1, knapsackInput, initState2, ShadowBootstrap.initState2]
      · simp [N1, hm2, hm3, s₀, knapsackInput, initState2, ShadowBootstrap.initState2]
  have hR_clean : Function.update s₀.R 0 ε' = (knapsackInput inst ε' ρ).R := by
    ext m
    rcases m with _ | m
    · simp [knapsackInput, initState2, ShadowBootstrap.initState2]
    · simp [s₀, knapsackInput, initState2, ShadowBootstrap.initState2]
  have p11 : P[11]? = some (Instr.rblt 1 0 21) := by rw [get_wrap Qs 11 (by omega)]; rfl
  have p30 : P[30]? = some (Instr.rsub 0 1 0) := by rw [get_wrap Qs 30 (by omega)]; rfl
  have p31 : P[31]? = some (Instr.rdiv 0 0 1) := by rw [get_wrap Qs 31 (by omega)]; rfl
  have p32 : P[32]? = some (Instr.nconst 2 0) := by rw [get_wrap Qs 32 (by omega)]; rfl
  by_cases hbranch : ρ < vA
  · -- True branch: (d - 1) / d < ε, so ε' = (d - 1) / d
    have hε'_eq : ε' = ((d : ℝ) - 1) / d := min_eq_right (hcond_iff.mp hbranch).le
    have st11 : run P ⟨11, Function.update s₀.R 0 vA, Function.update N1 3 0⟩ 1 =
        ⟨21, Function.update s₀.R 0 vA, Function.update N1 3 0⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [p11]
      simp [hs₀_R1, hbranch]
    have p21 : P[21]? = some (Instr.rconst 0 0) := by rw [get_wrap Qs 21 (by omega)]; rfl
    have p22 : P[22]? = some (Instr.nadd 3 0 4) := by rw [get_wrap Qs 22 (by omega)]; rfl
    have st21 : run P ⟨21, Function.update s₀.R 0 vA, Function.update N1 3 0⟩ 1 =
        ⟨22, Function.update s₀.R 0 0, Function.update N1 3 0⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [p21]; simp
    have st22 : run P ⟨22, Function.update s₀.R 0 0, Function.update N1 3 0⟩ 1 =
        ⟨23, Function.update s₀.R 0 0, Function.update N1 3 d⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [p22]
      simp [hN1_0, hN1_4]
    have hloopC := run_addLoop Qs 23 28
      (by rw [get_wrap Qs 23 (by omega)]; rfl)
      (by rw [get_wrap Qs 24 (by omega)]; rfl)
      (by rw [get_wrap Qs 25 (by omega)]; rfl)
      (by rw [get_wrap Qs 26 (by omega)]; rfl)
      (by rw [get_wrap Qs 27 (by omega)]; rfl)
      s₀.R N1 ρ hs₀_R1 hN1_2 hN1_4 d 0
    rw [zero_add] at hloopC
    have p28 : P[28]? = some (Instr.rdiv 0 1 0) := by rw [get_wrap Qs 28 (by omega)]; rfl
    have p29 : P[29]? = some (Instr.rmul 0 0 1) := by rw [get_wrap Qs 29 (by omega)]; rfl
    have st28_33 : run P ⟨28, Function.update s₀.R 0 ((d : ℝ) * ρ), Function.update N1 3 0⟩ 5 =
        ⟨33, Function.update s₀.R 0 ε', Function.update (Function.update N1 3 0) 2 0⟩ := by
      have hd_ne : (d : ℝ) ≠ 0 := by positivity
      have s28 : run P ⟨28, Function.update s₀.R 0 ((d : ℝ) * ρ), Function.update N1 3 0⟩ 1 =
          ⟨29, Function.update s₀.R 0 (ρ / ((d : ℝ) * ρ)), Function.update N1 3 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p28]; simp [hs₀_R1]
      have s29 : run P ⟨29, Function.update s₀.R 0 (ρ / ((d : ℝ) * ρ)), Function.update N1 3 0⟩ 1 =
          ⟨30, Function.update s₀.R 0 ((ρ / ((d : ℝ) * ρ)) * ρ), Function.update N1 3 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p29]; simp [hs₀_R1]
      have s30 : run P ⟨30, Function.update s₀.R 0 ((ρ / ((d : ℝ) * ρ)) * ρ), Function.update N1 3 0⟩ 1 =
          ⟨31, Function.update s₀.R 0 (ρ - (ρ / ((d : ℝ) * ρ)) * ρ), Function.update N1 3 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p30]; simp [hs₀_R1]
      have s31 : run P ⟨31, Function.update s₀.R 0 (ρ - (ρ / ((d : ℝ) * ρ)) * ρ), Function.update N1 3 0⟩ 1 =
          ⟨32, Function.update s₀.R 0 ε', Function.update N1 3 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p31]
        simp only [Function.update_self, Function.update_of_ne (by omega : (1 : ℕ) ≠ 0),
          hs₀_R1, Function.update_idem]
        congr 2
        rw [hε'_eq]
        field_simp [hρ0.ne', hd_ne]
      have s32 : run P ⟨32, Function.update s₀.R 0 ε', Function.update N1 3 0⟩ 1 =
          ⟨33, Function.update s₀.R 0 ε', Function.update (Function.update N1 3 0) 2 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p32]
      have h5 : (5 : ℕ) = 1 + (1 + (1 + (1 + 1))) := rfl
      rw [h5, run_add, s28, run_add, s29, run_add, s30, run_add, s31, s32]
    let tw := 6 + (4 * (d - 1) + 2) + 1 + 1 + 1 + (4 * d + 2) + 5
    refine ⟨tw, by dsimp [tw]; omega, ?_⟩
    have htw : tw = (6 + (4 * (d - 1) + 2)) + (1 + (1 + (1 + ((4 * d + 2) + 5)))) := by
      dsimp [tw]; omega
    rw [htw, run_add, h_to11, run_add, st11, run_add, st21, run_add, st22,
      run_add, hloopC, st28_33, hR_clean, hN_clean]
    rfl
  · -- False branch: ε ≤ (d - 1) / d, so ε' = ε
    have hε'_eq : ε' = ε := min_eq_left (not_lt.mp ( mt hcond_iff.mpr hbranch))
    have st11 : run P ⟨11, Function.update s₀.R 0 vA, Function.update N1 3 0⟩ 1 =
        ⟨12, Function.update s₀.R 0 vA, Function.update N1 3 0⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [p11]
      simp [hs₀_R1, hbranch]
    have p12 : P[12]? = some (Instr.nsub 3 0 2) := by rw [get_wrap Qs 12 (by omega)]; rfl
    have st12 : run P ⟨12, Function.update s₀.R 0 vA, Function.update N1 3 0⟩ 1 =
        ⟨13, Function.update s₀.R 0 vA, Function.update N1 3 (d - 1)⟩ := by
      rw [run_one]; unfold step; dsimp only []; rw [p12]
      simp [hN1_0, hN1_2]
    have hloopB := run_addLoop Qs 13 18
      (by rw [get_wrap Qs 13 (by omega)]; rfl)
      (by rw [get_wrap Qs 14 (by omega)]; rfl)
      (by rw [get_wrap Qs 15 (by omega)]; rfl)
      (by rw [get_wrap Qs 16 (by omega)]; rfl)
      (by rw [get_wrap Qs 17 (by omega)]; rfl)
      s₀.R N1 ρ hs₀_R1 hN1_2 hN1_4 (d - 1) vA
    have hvA_cancel : vA + ((d - 1 : ℕ) : ℝ) * ρ = ρ / (1 - ε) := by dsimp [vA]; ring
    rw [hvA_cancel] at hloopB
    have p18 : P[18]? = some (Instr.rdiv 0 1 0) := by rw [get_wrap Qs 18 (by omega)]; rfl
    have p19 : P[19]? = some (Instr.rmul 0 0 1) := by rw [get_wrap Qs 19 (by omega)]; rfl
    have p20 : P[20]? = some (Instr.nblt 4 2 30) := by rw [get_wrap Qs 20 (by omega)]; rfl
    have st18_33 : run P ⟨18, Function.update s₀.R 0 (ρ / (1 - ε)), Function.update N1 3 0⟩ 6 =
        ⟨33, Function.update s₀.R 0 ε', Function.update (Function.update N1 3 0) 2 0⟩ := by
      have h1e : 1 - ε ≠ 0 := by linarith
      have s18 : run P ⟨18, Function.update s₀.R 0 (ρ / (1 - ε)), Function.update N1 3 0⟩ 1 =
          ⟨19, Function.update s₀.R 0 (ρ / (ρ / (1 - ε))), Function.update N1 3 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p18]; simp [hs₀_R1]
      have s19 : run P ⟨19, Function.update s₀.R 0 (ρ / (ρ / (1 - ε))), Function.update N1 3 0⟩ 1 =
          ⟨20, Function.update s₀.R 0 ((ρ / (ρ / (1 - ε))) * ρ), Function.update N1 3 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p19]; simp [hs₀_R1]
      have s20 : run P ⟨20, Function.update s₀.R 0 ((ρ / (ρ / (1 - ε))) * ρ), Function.update N1 3 0⟩ 1 =
          ⟨30, Function.update s₀.R 0 ((ρ / (ρ / (1 - ε))) * ρ), Function.update N1 3 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p20]; simp [hN1_4, hN1_2]
      have s30 : run P ⟨30, Function.update s₀.R 0 ((ρ / (ρ / (1 - ε))) * ρ), Function.update N1 3 0⟩ 1 =
          ⟨31, Function.update s₀.R 0 (ρ - (ρ / (ρ / (1 - ε))) * ρ), Function.update N1 3 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p30]; simp [hs₀_R1]
      have s31 : run P ⟨31, Function.update s₀.R 0 (ρ - (ρ / (ρ / (1 - ε))) * ρ), Function.update N1 3 0⟩ 1 =
          ⟨32, Function.update s₀.R 0 ε', Function.update N1 3 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p31]
        simp only [Function.update_self, Function.update_of_ne (by omega : (1 : ℕ) ≠ 0),
          hs₀_R1, Function.update_idem]
        congr 2
        rw [hε'_eq]
        field_simp [hρ0.ne', h1e]
        ring
      have s32 : run P ⟨32, Function.update s₀.R 0 ε', Function.update N1 3 0⟩ 1 =
          ⟨33, Function.update s₀.R 0 ε', Function.update (Function.update N1 3 0) 2 0⟩ := by
        rw [run_one]; unfold step; dsimp only []; rw [p32]
      have h6 : (6 : ℕ) = 1 + (1 + (1 + (1 + (1 + 1)))) := rfl
      rw [h6, run_add, s18, run_add, s19, run_add, s20, run_add, s30, run_add, s31, s32]
    let tw := 6 + (4 * (d - 1) + 2) + 1 + 1 + (4 * (d - 1) + 2) + 6
    refine ⟨tw, by dsimp [tw]; omega, ?_⟩
    have htw : tw = (6 + (4 * (d - 1) + 2)) + (1 + (1 + ((4 * (d - 1) + 2) + 6))) := by
      dsimp [tw]; omega
    rw [htw, run_add, h_to11, run_add, st11, run_add, st12,
      run_add, hloopB, st18_33, hR_clean, hN_clean]
    rfl

lemma two_pow_ge_add_two : ∀ d : ℕ, 2 ≤ d → d + 2 ≤ 2 ^ d
  | 2, _ => by norm_num
  | d + 1, hd => by
    by_cases h2 : 2 ≤ d
    · have ih := two_pow_ge_add_two d h2
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega
    · have hd2 : d = 1 := by omega
      subst hd2; norm_num

lemma mainBound_absorb (d n : ℕ) (hd : 2 ≤ d) (ε ρ C₀ : ℝ)
    (hC₀ : 0 < C₀) (hε0 : 0 < ε) (hε1 : ε < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    let ε' := min ε (((d : ℝ) - 1) / d)
    (8 * (d : ℝ) + 16) + mainBound d n ε' ρ C₀ ≤ mainBound d n ε ρ (2 * C₀ + 4) := by
  intro ε'
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hNN : 2 ≤ NN n := le_max_right _ _
  have hNN1 : 1 ≤ NN n := by linarith
  have hlog : 1 ≤ Real.logb 2 (NN n) := by
    have h1 : Real.logb 2 2 ≤ Real.logb 2 (NN n) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) hNN
    rwa [Real.logb_self_eq_one (by norm_num)] at h1
  have hρε_pos : 0 < ρ * ε := mul_pos hρ0 hε0
  have hρε_lt1 : ρ * ε < 1 := by nlinarith
  let B : ℝ := (d : ℝ) * Real.logb 2 (NN n) / (ρ * ε)
  have hB_gt2 : 2 < B := by
    dsimp [B]
    rw [lt_div_iff₀ hρε_pos]
    nlinarith
  have hB_pos : 0 < B := by linarith
  let F : ℝ := NN n ^ (⌈((d : ℝ) - 1) / (2 * ε) - 1 / 2 + ρ⌉) + NN n ^ d
  have hpow_z_nonneg : 0 ≤ NN n ^ (⌈((d : ℝ) - 1) / (2 * ε) - 1 / 2 + ρ⌉) := by positivity
  have hNNd_ge : (2 : ℝ) ^ d ≤ NN n ^ d := pow_le_pow_left₀ (by norm_num) hNN d
  have hd2_le_2d : (d : ℝ) + 2 ≤ (2 : ℝ) ^ d := by exact_mod_cast two_pow_ge_add_two d hd
  have hF_ge_2d : (2 : ℝ) ^ d ≤ F := by dsimp [F]; linarith
  -- Bound mainBound d n ε' ρ C₀ ≤ 2 * F * B ^ (2 * C₀ * d)
  have hmb_le : mainBound d n ε' ρ C₀ ≤ 2 * F * B ^ (2 * C₀ * (d : ℝ)) := by
    by_cases hle : ε ≤ ((d : ℝ) - 1) / d
    · have hε'_eq : ε' = ε := min_eq_left hle
      rw [hε'_eq]
      unfold mainBound
      change F * B ^ (C₀ * (d : ℝ)) ≤ 2 * F * B ^ (2 * C₀ * (d : ℝ))
      have hpow_le : B ^ (C₀ * (d : ℝ)) ≤ B ^ (2 * C₀ * (d : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
      have hF_nonneg : 0 ≤ F := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
      have hBpow_nonneg : 0 ≤ B ^ (2 * C₀ * (d : ℝ)) := by positivity
      calc F * B ^ (C₀ * (d : ℝ))
          ≤ F * B ^ (2 * C₀ * (d : ℝ)) := mul_le_mul_of_nonneg_left hpow_le hF_nonneg
        _ ≤ 2 * F * B ^ (2 * C₀ * (d : ℝ)) := by nlinarith
    · have hε'_eq : ε' = ((d : ℝ) - 1) / d := min_eq_right (le_of_not_ge hle)
      rw [hε'_eq]
      unfold mainBound
      -- First factor: ceiling ≤ d
      have hdiv_simp : ((d : ℝ) - 1) / (2 * (((d : ℝ) - 1) / d)) = (d : ℝ) / 2 := by
        have hd1_ne : (d : ℝ) - 1 ≠ 0 := by linarith
        have hd_ne : (d : ℝ) ≠ 0 := by linarith
        field_simp [hd1_ne, hd_ne]
      have hceil_le_d : ⌈((d : ℝ) - 1) / (2 * (((d : ℝ) - 1) / d)) - 1 / 2 + ρ⌉ ≤ (d : ℤ) := by
        rw [hdiv_simp, Int.ceil_le]
        push_cast
        linarith
      have hzpow_le : NN n ^ (⌈((d : ℝ) - 1) / (2 * (((d : ℝ) - 1) / d)) - 1 / 2 + ρ⌉) ≤ NN n ^ d := by
        calc NN n ^ (⌈((d : ℝ) - 1) / (2 * (((d : ℝ) - 1) / d)) - 1 / 2 + ρ⌉)
            ≤ NN n ^ (d : ℤ) := zpow_le_zpow_right₀ hNN1 hceil_le_d
          _ = NN n ^ d := zpow_natCast (NN n) d
      have hF'_le : NN n ^ (⌈((d : ℝ) - 1) / (2 * (((d : ℝ) - 1) / d)) - 1 / 2 + ρ⌉) + NN n ^ d ≤ 2 * F := by
        dsimp [F]; linarith
      -- Second factor: B' ≤ 2 * B ≤ B ^ 2
      let B' : ℝ := (d : ℝ) * Real.logb 2 (NN n) / (ρ * (((d : ℝ) - 1) / d))
      have hε'_pos : 0 < ((d : ℝ) - 1) / d := div_pos (by linarith) (by linarith)
      have hB'_nonneg : 0 ≤ B' := by
        dsimp [B']
        exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_pos hρ0 hε'_pos).le
      have hB'_le_B2 : B' ≤ B ^ (2 : ℝ) := by
        have hd_pos : (0 : ℝ) < d := by linarith
        have h2ε_le : ε ≤ 2 * (((d : ℝ) - 1) / d) := by
          have h1le : (1 : ℝ) ≤ 2 * (((d : ℝ) - 1) / d) := by
            rw [show 2 * (((d : ℝ) - 1) / d) = (2 * (d : ℝ) - 2) / d by ring, le_div_iff₀ hd_pos]
            linarith
          linarith
        have hB'_le_2B : B' ≤ 2 * B := by
          dsimp [B', B]
          have hnum_nonneg : 0 ≤ (d : ℝ) * Real.logb 2 (NN n) := mul_nonneg (by linarith) (by linarith)
          rw [show (2 : ℝ) * ((d : ℝ) * Real.logb 2 (NN n) / (ρ * ε)) =
              (2 * ((d : ℝ) * Real.logb 2 (NN n))) / (ρ * ε) by ring]
          rw [div_le_div_iff₀ (mul_pos hρ0 hε'_pos) hρε_pos]
          have hden_le : ρ * ε ≤ 2 * (ρ * (((d : ℝ) - 1) / d)) := by nlinarith
          have hmul := mul_le_mul_of_nonneg_left hden_le hnum_nonneg
          linarith
        rw [Real.rpow_two]
        nlinarith
      have hpow'_le : B' ^ (C₀ * (d : ℝ)) ≤ B ^ (2 * C₀ * (d : ℝ)) := by
        calc B' ^ (C₀ * (d : ℝ))
            ≤ (B ^ (2 : ℝ)) ^ (C₀ * (d : ℝ)) :=
              Real.rpow_le_rpow hB'_nonneg hB'_le_B2 (by positivity)
          _ = B ^ (2 * C₀ * (d : ℝ)) := by rw [← Real.rpow_mul hB_pos.le]; ring_nf
      exact mul_le_mul hF'_le hpow'_le (by positivity) (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d])
  -- Now compare with F * B ^ ((2 * C₀ + 4) * d)
  have hB4 : 16 ≤ B ^ (4 * (d : ℝ)) := by
    calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
      _ ≤ B ^ (4 : ℝ) := Real.rpow_le_rpow (by norm_num) hB_gt2.le (by norm_num)
      _ ≤ B ^ (4 * (d : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hB_split : B ^ ((2 * C₀ + 4) * (d : ℝ)) = B ^ (2 * C₀ * (d : ℝ)) * B ^ (4 * (d : ℝ)) := by
    rw [show (2 * C₀ + 4) * (d : ℝ) = 2 * C₀ * (d : ℝ) + 4 * (d : ℝ) by ring,
      Real.rpow_add hB_pos]
  have hB2C_ge1 : 1 ≤ B ^ (2 * C₀ * (d : ℝ)) :=
    Real.one_le_rpow (by linarith) (by positivity)
  have hF_nonneg : 0 ≤ F := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
  have h16 : 16 * F * B ^ (2 * C₀ * (d : ℝ)) ≤ mainBound d n ε ρ (2 * C₀ + 4) := by
    unfold mainBound
    change 16 * F * B ^ (2 * C₀ * (d : ℝ)) ≤ F * B ^ ((2 * C₀ + 4) * (d : ℝ))
    rw [hB_split]
    have : 16 * B ^ (2 * C₀ * (d : ℝ)) ≤ B ^ (2 * C₀ * (d : ℝ)) * B ^ (4 * (d : ℝ)) := by nlinarith
    nlinarith
  have h14 : 8 * (d : ℝ) + 16 ≤ 14 * F * B ^ (2 * C₀ * (d : ℝ)) := by
    have h1 : 8 * (d : ℝ) + 16 ≤ 14 * ((d : ℝ) + 2) := by linarith
    have h2 : 14 * ((d : ℝ) + 2) ≤ 14 * F := by linarith
    nlinarith
  linarith

end Aux11

open VecKnapsackMitM.Main MatMulTimeLP

theorem solution :
    ∃ P : Program, VecBalPoly.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ), 2 ≤ d → ∀ (ε ρ : ℝ), 0 < ε → ε < 1 → 0 < ρ → ρ < 1 →
        ∀ inst : Instance d n, inst.Nonneg →
          RunsWithin P (knapsackInput inst ε ρ) (mainBound d n ε ρ C)
            (fun s => OutputBinary s n ∧ inst.IsApprox ε (outputSet s n)) := by
  obtain ⟨P47, hAdm47, C0, hC0, hRun47⟩ := lemma_4_7
  let P : Program := Aux11.wrapProg ++ Aux11.shiftProg Aux11.wrapProg.length P47
  have hAdmP : VecBalPoly.Admissible P := by
    intro ins hins
    rcases List.mem_append.mp hins with hw | hs
    · exact Aux11.wrapProg_admissible ins hw
    · exact Aux11.shiftProg_admissible Aux11.wrapProg.length hAdm47 ins hs
  refine ⟨P, hAdmP, 2 * C0 + 4, by linarith, ?_⟩
  intro d n hd ε ρ hε0 hε1 hρ0 hρ1 inst hinst
  let ε' : ℝ := min ε (((d : ℝ) - 1) / d)
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hε'0 : 0 < ε' := lt_min hε0 (div_pos (by linarith) (by linarith))
  have hε'_le_cap : ε' ≤ ((d : ℝ) - 1) / d := min_le_right _ _
  have hε'1 : ε' < 1 := lt_of_le_of_lt hε'_le_cap (by rw [div_lt_one (by linarith)]; linarith)
  obtain ⟨tw, htw_le, hwrap_run⟩ := Aux11.run_wrapProg hd inst hε0 hε1 hρ0 P47
  obtain ⟨t47, hHalted47, ht47_le, hOutBin, hAlg3⟩ :=
    hRun47 d n hd ε' ρ hε'0 hε'1 hρ0 hρ1 inst hinst
  have hApprox' : inst.IsApprox ε' (outputSet (run P47 (knapsackInput inst ε' ρ) t47) n) :=
    lemma_4_6 d n hd ρ ε' hρ0 hρ1 hε'0 hε'_le_cap inst hinst _ hAlg3
  have hApprox : inst.IsApprox ε (outputSet (run P47 (knapsackInput inst ε' ρ) t47) n) := by
    refine ⟨hApprox'.1, fun S' hS' => ?_⟩
    have hprof_nonneg : 0 ≤ inst.toItems.profit S' :=
      Finset.sum_nonneg fun i _ => hinst.1.1 i
    have hε'_le_ε : ε' ≤ ε := min_le_left _ _
    calc (1 - ε) * inst.toItems.profit S'
        ≤ (1 - ε') * inst.toItems.profit S' :=
          mul_le_mul_of_nonneg_right (by linarith) hprof_nonneg
      _ ≤ inst.toItems.profit (outputSet (run P47 (knapsackInput inst ε' ρ) t47) n) :=
          hApprox'.2 S' hS'
  refine ⟨tw + t47, ?_, ?_, ?_⟩
  · rw [Aux11.run_add, hwrap_run, Aux11.run_append_shift]
    exact Aux11.isHalted_append_shift _ _ _ hHalted47
  · have htw_real : (tw : ℝ) ≤ 8 * (d : ℝ) + 16 := by exact_mod_cast htw_le
    have habs := Aux11.mainBound_absorb d n hd ε ρ C0 hC0 hε0 hε1 hρ0 hρ1
    push_cast
    linarith
  · change OutputBinary (run P (knapsackInput inst ε ρ) (tw + t47)) n ∧
        inst.IsApprox ε (outputSet (run P (knapsackInput inst ε ρ) (tw + t47)) n)
    rw [Aux11.run_add, hwrap_run, Aux11.run_append_shift]
    exact ⟨hOutBin, hApprox⟩
