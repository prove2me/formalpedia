-- Prove2me | solution 1 for PNormRegLib.reloc_sim
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:45:00.352179+00:00
-- url     : https://prove2.me/submissions/10c18ac8-adf6-427b-b2d6-fe4e8eca78eb

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_PNormRegLib_Simulation
import Theorems.Thm_PNormRegLib_step_eq_exec
import Theorems.Thm_PNormRegLib_bounded_run
import Theorems.Thm_PNormRegLib_sim_exec
import Theorems.Thm_PNormRegLib_sim_halt
import Definitions.Def_PNormRegLib_Exec

open PNormReg PNormRegLib SmaleNinth

namespace PNormRegLibRunAux

lemma stepE {P : Program} {ω : ℕ → Bool} {s : State} {ins : Instr}
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) : step P ω s = exec ω ins s :=
  step_eq_exec P ω s ins hh h

lemma bounded_step {P : Program} {ω : ℕ → Bool} {X : ℤ} {s : State} (hs : PBounded X s)
    (hlit : LitBound P X) (hX : 1 ≤ X) : PBounded (2 * X) (step P ω s) := by
  have := bounded_run P ω X s hs hlit hX 1
  rwa [pow_one, mul_comm] at this

lemma LitBound.mono' {P : Program} {L L' : ℤ} (h : LitBound P L) (hL : L ≤ L') : LitBound P L' :=
  fun q c hc => (h q c hc).trans hL

/-- At a missing or `accept`/`reject` instruction the machine is stuck: only `work` changes. -/
def Stuck (P : Program) (pc : ℕ) : Prop :=
  P[pc]? = none ∨ P[pc]? = some (.core .accept) ∨ P[pc]? = some (.core .reject)

lemma run_stuck {P : Program} {ω : ℕ → Bool} {s : State} (hh : s.halted = false)
    (hs : Stuck P s.core.pc) : ∀ t, (run P s ω t).halted = false ∧ (run P s ω t).core.pc = s.core.pc
  | 0 => ⟨hh, rfl⟩
  | t + 1 => by
    obtain ⟨h1, h2⟩ := run_stuck (ω := ω) hh hs t
    have key : ∀ u : State, u.halted = false → u.core.pc = s.core.pc →
        (step P ω u).halted = false ∧ (step P ω u).core.pc = s.core.pc := by
      intro u hu hp
      rcases hs with h | h | h
      · rw [← hp] at h; simp [step, hu, h]; exact hp
      · rw [← hp] at h; rw [stepE hu h]; simp [exec, coreExec, hu, hp]
      · rw [← hp] at h; rw [stepE hu h]; simp [exec, coreExec, hu, hp]
    have : run P s ω (t + 1) = step P ω (run P s ω t) := by
      simp only [run, Function.iterate_succ_apply']
    rw [this]
    exact key _ h1 h2

lemma run_succ (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ) :
    run P s ω (t + 1) = run P (step P ω s) ω t := by
  simp only [run, Function.iterate_succ_apply]

lemma run_add (P : Program) (s : State) (ω : ℕ → Bool) (t u : ℕ) :
    run P s ω (t + u) = run P (run P s ω u) ω t := by
  simp only [run, Function.iterate_add_apply]

/-- A halted state stutters forever. -/
lemma run_of_halted {P : Program} {ω : ℕ → Bool} {s : State} (h : s.halted = true) :
    ∀ t, run P s ω t = s
  | 0 => rfl
  | t + 1 => by rw [run_succ, show step P ω s = s by simp [step, h]]; exact run_of_halted h t

lemma getElem?_pairs {α β : Type*} (f g : α → β) :
    ∀ (L : List α) (i : ℕ), (L.flatMap fun x => [f x, g x])[2 * i]? = L[i]?.map f ∧
      (L.flatMap fun x => [f x, g x])[2 * i + 1]? = L[i]?.map g
  | [], i => by simp
  | a :: L, 0 => by simp
  | a :: L, i + 1 => by
    obtain ⟨h1, h2⟩ := getElem?_pairs f g L i
    simp only [List.flatMap_cons, List.cons_append, List.nil_append,
      show 2 * (i + 1) = 2 * i + 1 + 1 by ring, show 2 * i + 1 + 1 + 1 = 2 * i + 1 + 1 + 1 from rfl,
      List.getElem?_cons_succ, List.length_cons]
    exact ⟨h1, h2⟩

lemma reloc_fetch {p : RelocParams} {P Q : Program} {pc : ℕ} {ins : Instr}
    (hE : Embeds Q (reloc p P) p.cOff) (h : P[pc]? = some ins) :
    Q[p.cOff + 2 * pc]? = some (p.pair ins).1 ∧ Q[p.cOff + 2 * pc + 1]? = some (p.pair ins).2 := by
  obtain ⟨h1, h2⟩ := getElem?_pairs (fun ins => (p.pair ins).1) (fun ins => (p.pair ins).2) P pc
  rw [h] at h1 h2
  exact ⟨hE _ _ h1, by rw [add_assoc]; exact hE _ _ h2⟩

/-- The preparation instruction only advances the program counter (and may set `tmp`). -/
lemma prep_exec (p : RelocParams) (ω : ℕ → Bool) (ins : Instr) (r : State) :
    (exec ω (p.pair ins).1 r).halted = r.halted ∧
      (exec ω (p.pair ins).1 r).core.pc = r.core.pc + 1 := by
  cases ins with
  | core i => cases i <;> simp [RelocParams.pair, RelocParams.noop, exec, coreExec]
  | _ => simp [RelocParams.pair, RelocParams.noop, exec, coreExec]

end PNormRegLibRunAux

open PNormRegLibRunAux in
theorem solution (p : RelocParams) (F : Frame) (P Q : Program) (ω : ℕ → Bool) (X : ℤ)
    (hE : Embeds Q (reloc p P) p.cOff) (hV : Valid p F) (hU : UsesBelow P F.nR F.nQ)
    (hlit : LitBound P X) (hX : 1 ≤ X) (t : ℕ) (Y : ℤ) (r v : State) (hS : Sim p F r v)
    (hB : PBounded Y v) (hXY : X ≤ Y) (hR : Y * 2 ^ t ≤ F.R)
    (hh : (run P v (fun i => ω (i + F.k)) t).halted = true) :
    ∃ t', Agree p F (run Q r ω t') (run P v (fun i => ω (i + F.k)) t) ∧
      (run Q r ω t').core.pc = p.exit ∧ (run Q r ω t').halted = false := by
  induction t generalizing Y r v with
  | zero =>
    simp [run, hS.2.2.1] at hh
  | succ t ih =>
    obtain ⟨hA, hrh, hvh, hpc⟩ := hS
    have hY1 : (1 : ℤ) ≤ Y := hX.trans hXY
    have hpow : (1 : ℤ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
    have hYR : Y ≤ F.R := by
      have : Y ≤ Y * 2 ^ (t + 1) := le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
      linarith
    -- the current instruction is live
    have hlive : ¬ Stuck P v.core.pc := by
      intro hst
      have := (run_stuck (ω := fun i => ω (i + F.k)) hvh hst (t + 1)).1
      rw [hh] at this; exact Bool.noConfusion this
    obtain ⟨ins, hins⟩ : ∃ ins, P[v.core.pc]? = some ins := by
      cases h : P[v.core.pc]? with
      | none => exact absurd (Or.inl h) hlive
      | some ins => exact ⟨ins, rfl⟩
    have hna : ins ≠ .core .accept := fun e => hlive (Or.inr (Or.inl (e ▸ hins)))
    have hnr : ins ≠ .core .reject := fun e => hlive (Or.inr (Or.inr (e ▸ hins)))
    obtain ⟨hf1, hf2⟩ := reloc_fetch hE hins
    obtain ⟨hp1, hp2⟩ := prep_exec p ω ins r
    -- two real steps
    have hr2 : run Q r ω 2 = exec ω (p.pair ins).2 (exec ω (p.pair ins).1 r) := by
      show step Q ω (step Q ω r) = _
      rw [stepE hrh (by rw [hpc]; exact hf1)]
      exact stepE (by rw [hp1, hrh]) (by rw [hp2, hpc]; exact hf2)
    have hv1 : step P (fun i => ω (i + F.k)) v = exec (fun i => ω (i + F.k)) ins v :=
      stepE hvh hins
    rw [run_succ, hv1] at hh ⊢
    by_cases hhalt : ins = .halt
    · subst hhalt
      obtain ⟨hA', hpc', hrh', hvh'⟩ := sim_halt p F ω r v hA
      refine ⟨2, ?_⟩
      rw [hr2, run_of_halted hvh']
      exact ⟨hA', hpc', hrh'.trans hrh⟩
    · obtain ⟨hA', hpc', hrh', hvh'⟩ :=
        sim_exec p F ω ins Y r v hV (hU ins (List.mem_of_getElem? hins)) hA hpc hB hYR ⟨hna, hnr, hhalt⟩
      have hB' : PBounded (2 * Y) (exec (fun i => ω (i + F.k)) ins v) := by
        rw [← hv1]; exact bounded_step hB (LitBound.mono' hlit hXY) hY1
      obtain ⟨t', ht'⟩ := ih (2 * Y) _ _ ⟨hA', hrh'.trans hrh, hvh'.trans hvh, hpc'⟩ hB'
        (by linarith) (by rw [pow_succ] at hR; linarith) hh
      refine ⟨t' + 2, ?_⟩
      rw [run_add, hr2]
      exact ht'
