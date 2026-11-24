-- Prove2me | solution 1 for WilliamsonShmoys.sandbox_odd_simulation
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T10:20:06.191661+00:00
-- url     : https://prove2.me/submissions/f75bb3ad-e29b-4cf5-932b-482a4eb0fedf

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSandboxOdd
set_option autoImplicit false
namespace SBO
open WilliamsonShmoys PlanarRAMInstruction

noncomputable def execI : PlanarRAMInstruction → PlanarRAMState → PlanarRAMState
  | natConst dst value, s => { s with pc := s.pc + 1, natMem := Function.update s.natMem dst value }
  | natAdd dst l r, s => { s with pc := s.pc + 1, natMem := Function.update s.natMem dst (s.natMem l + s.natMem r) }
  | natSub dst l r, s => { s with pc := s.pc + 1, natMem := Function.update s.natMem dst (s.natMem l - s.natMem r) }
  | natLoad dst a, s => { s with pc := s.pc + 1, natMem := Function.update s.natMem dst (s.natMem (s.natMem a)) }
  | natStore a src, s => { s with pc := s.pc + 1, natMem := Function.update s.natMem (s.natMem a) (s.natMem src) }
  | realZero dst, s => { s with pc := s.pc + 1, realMem := Function.update s.realMem dst 0 }
  | realAdd dst l r, s => { s with pc := s.pc + 1, realMem := Function.update s.realMem dst (s.realMem l + s.realMem r) }
  | realSub dst l r, s => { s with pc := s.pc + 1, realMem := Function.update s.realMem dst (s.realMem l - s.realMem r) }
  | realLoad dst a, s => { s with pc := s.pc + 1, realMem := Function.update s.realMem dst (s.realMem (s.natMem a)) }
  | realStore a src, s => { s with pc := s.pc + 1, realMem := Function.update s.realMem (s.natMem a) (s.realMem src) }
  | natBranch l r y n, s => { s with pc := if s.natMem l ≤ s.natMem r then y else n }
  | realBranch l r y n, s => { s with pc := if s.realMem l ≤ s.realMem r then y else n }
  | jump j, s => { s with pc := j }
  | halt, s => s

lemma step_eq (p : List PlanarRAMInstruction) (s : PlanarRAMState) (ins : PlanarRAMInstruction)
    (h : p[s.pc]? = some ins) : planarRAMStep p s = execI ins s := by
  unfold planarRAMStep
  rw [h]
  cases ins <;> rfl



variable {α : Type}

lemma upd_rel (M M' : ℕ → α) (d : ℕ) (x : α) (h : ∀ a, M' (2 * a + 1) = M a) :
    ∀ a, Function.update M' (2 * d + 1) x (2 * a + 1) = Function.update M d x a := by
  intro a
  by_cases had : a = d
  · subst had; simp
  · rw [Function.update_of_ne (fun e => had (by omega)), Function.update_of_ne had, h]

lemma upd_relT (M' : ℕ → α) (T : ℕ) (x : α) (hT : T % 2 = 0) :
    ∀ a, Function.update M' T x (2 * a + 1) = M' (2 * a + 1) := by
  intro a
  exact Function.update_of_ne (by omega) _ _

lemma run1 (p : List PlanarRAMInstruction) (s : PlanarRAMState) :
    planarRAMRun p s 1 = planarRAMStep p s := rfl

lemma run2 (p : List PlanarRAMInstruction) (s : PlanarRAMState) :
    planarRAMRun p s 2 = planarRAMStep p (planarRAMStep p s) := rfl

lemma run3 (p : List PlanarRAMInstruction) (s : PlanarRAMState) :
    planarRAMRun p s 3 = planarRAMStep p (planarRAMStep p (planarRAMStep p s)) := rfl

/-- The scratch computation `T := 2*x + 1` done by the first two instructions of an
indirect-access block. -/
lemma scratch_eq (M' : ℕ → ℕ) (T ONE a0 x : ℕ) (hOT : ONE ≠ T) (hONE : M' ONE = 1)
    (hx : M' (2 * a0 + 1) = x) :
    Function.update (Function.update M' T (M' (2 * a0 + 1) + M' (2 * a0 + 1))) T
      (Function.update M' T (M' (2 * a0 + 1) + M' (2 * a0 + 1)) T +
        Function.update M' T (M' (2 * a0 + 1) + M' (2 * a0 + 1)) ONE) =
    Function.update M' T (2 * x + 1) := by
  rw [Function.update_idem, Function.update_self, Function.update_of_ne hOT, hONE, hx]
  congr 1
  omega

/-- One step of the subprogram is simulated by at most three host steps. -/
lemma sim_step (p q : List PlanarRAMInstruction) (base T ONE exit : ℕ)
    (hTe : T % 2 = 0) (hOe : ONE % 2 = 0) (hTO : T ≠ ONE)
    (hp : SandboxedOddAt p q base T ONE exit) (s s' : PlanarRAMState) (ins : PlanarRAMInstruction)
    (hq : q[s.pc]? = some ins) (hins : ins ≠ halt)
    (hrel : SandboxOddRel ONE s s') (hpc : s'.pc = base + 3 * s.pc) :
    ∃ τ, τ ≤ 3 ∧
      (planarRAMRun p s' τ).pc = base + 3 * (planarRAMStep q s).pc ∧
      SandboxOddRel ONE (planarRAMStep q s) (planarRAMRun p s' τ) ∧
      (∀ a, a % 2 = 0 → a ≠ T → (planarRAMRun p s' τ).natMem a = s'.natMem a) ∧
      (∀ a, a % 2 = 0 → (planarRAMRun p s' τ).realMem a = s'.realMem a) := by
  have hOT : ONE ≠ T := Ne.symm hTO
  obtain ⟨h1, h2, h3⟩ := hp s.pc ins hq
  rw [← hpc] at h1
  have h2' : p[s'.pc + 1]? = some (sandboxTriple base T ONE exit s.pc ins).2.1 := by
    rw [hpc]; exact h2
  have h3' : p[s'.pc + 1 + 1]? = some (sandboxTriple base T ONE exit s.pc ins).2.2 := by
    rw [hpc]; exact h3
  obtain ⟨hO', hn, hr⟩ := hrel
  rw [step_eq q s ins hq]
  cases ins with
  | natConst d v =>
    refine ⟨2, by norm_num, ?_⟩
    rw [run2, step_eq p s' _ h1, step_eq p _ _ (by simpa [execI, sandboxTriple] using h2')]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | natAdd d l r =>
    refine ⟨2, by norm_num, ?_⟩
    rw [run2, step_eq p s' _ h1, step_eq p _ _ (by simpa [execI, sandboxTriple] using h2')]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | natSub d l r =>
    refine ⟨2, by norm_num, ?_⟩
    rw [run2, step_eq p s' _ h1, step_eq p _ _ (by simpa [execI, sandboxTriple] using h2')]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | natLoad d a0 =>
    refine ⟨3, le_rfl, ?_⟩
    have e1 : planarRAMStep p s' = execI (sandboxTriple base T ONE exit s.pc (natLoad d a0)).1 s' := step_eq p s' _ h1
    have e2 : planarRAMStep p (execI (sandboxTriple base T ONE exit s.pc (natLoad d a0)).1 s') = execI (sandboxTriple base T ONE exit s.pc (natLoad d a0)).2.1 (execI (sandboxTriple base T ONE exit s.pc (natLoad d a0)).1 s') :=
      step_eq p _ _ (by simpa [execI, sandboxTriple] using h2')
    have e3 : planarRAMStep p (execI (sandboxTriple base T ONE exit s.pc (natLoad d a0)).2.1 (execI (sandboxTriple base T ONE exit s.pc (natLoad d a0)).1 s')) =
        execI (sandboxTriple base T ONE exit s.pc (natLoad d a0)).2.2 (execI (sandboxTriple base T ONE exit s.pc (natLoad d a0)).2.1 (execI (sandboxTriple base T ONE exit s.pc (natLoad d a0)).1 s')) :=
      step_eq p _ _ (by simpa [execI, sandboxTriple] using h3')
    rw [run3, e1, e2, e3]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try rw [scratch_eq s'.natMem T ONE a0 (s.natMem a0) hOT hO' (hn a0)])
    all_goals (try simp only [Function.update_self])
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | natStore a0 src =>
    refine ⟨3, le_rfl, ?_⟩
    have e1 : planarRAMStep p s' = execI (sandboxTriple base T ONE exit s.pc (natStore a0 src)).1 s' := step_eq p s' _ h1
    have e2 : planarRAMStep p (execI (sandboxTriple base T ONE exit s.pc (natStore a0 src)).1 s') = execI (sandboxTriple base T ONE exit s.pc (natStore a0 src)).2.1 (execI (sandboxTriple base T ONE exit s.pc (natStore a0 src)).1 s') :=
      step_eq p _ _ (by simpa [execI, sandboxTriple] using h2')
    have e3 : planarRAMStep p (execI (sandboxTriple base T ONE exit s.pc (natStore a0 src)).2.1 (execI (sandboxTriple base T ONE exit s.pc (natStore a0 src)).1 s')) =
        execI (sandboxTriple base T ONE exit s.pc (natStore a0 src)).2.2 (execI (sandboxTriple base T ONE exit s.pc (natStore a0 src)).2.1 (execI (sandboxTriple base T ONE exit s.pc (natStore a0 src)).1 s')) :=
      step_eq p _ _ (by simpa [execI, sandboxTriple] using h3')
    rw [run3, e1, e2, e3]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try rw [scratch_eq s'.natMem T ONE a0 (s.natMem a0) hOT hO' (hn a0)])
    all_goals (try simp only [Function.update_self])
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | realZero d =>
    refine ⟨2, by norm_num, ?_⟩
    rw [run2, step_eq p s' _ h1, step_eq p _ _ (by simpa [execI, sandboxTriple] using h2')]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | realAdd d l r =>
    refine ⟨2, by norm_num, ?_⟩
    rw [run2, step_eq p s' _ h1, step_eq p _ _ (by simpa [execI, sandboxTriple] using h2')]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | realSub d l r =>
    refine ⟨2, by norm_num, ?_⟩
    rw [run2, step_eq p s' _ h1, step_eq p _ _ (by simpa [execI, sandboxTriple] using h2')]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | realLoad d a0 =>
    refine ⟨3, le_rfl, ?_⟩
    have e1 : planarRAMStep p s' = execI (sandboxTriple base T ONE exit s.pc (realLoad d a0)).1 s' := step_eq p s' _ h1
    have e2 : planarRAMStep p (execI (sandboxTriple base T ONE exit s.pc (realLoad d a0)).1 s') = execI (sandboxTriple base T ONE exit s.pc (realLoad d a0)).2.1 (execI (sandboxTriple base T ONE exit s.pc (realLoad d a0)).1 s') :=
      step_eq p _ _ (by simpa [execI, sandboxTriple] using h2')
    have e3 : planarRAMStep p (execI (sandboxTriple base T ONE exit s.pc (realLoad d a0)).2.1 (execI (sandboxTriple base T ONE exit s.pc (realLoad d a0)).1 s')) =
        execI (sandboxTriple base T ONE exit s.pc (realLoad d a0)).2.2 (execI (sandboxTriple base T ONE exit s.pc (realLoad d a0)).2.1 (execI (sandboxTriple base T ONE exit s.pc (realLoad d a0)).1 s')) :=
      step_eq p _ _ (by simpa [execI, sandboxTriple] using h3')
    rw [run3, e1, e2, e3]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try rw [scratch_eq s'.natMem T ONE a0 (s.natMem a0) hOT hO' (hn a0)])
    all_goals (try simp only [Function.update_self])
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | realStore a0 src =>
    refine ⟨3, le_rfl, ?_⟩
    have e1 : planarRAMStep p s' = execI (sandboxTriple base T ONE exit s.pc (realStore a0 src)).1 s' := step_eq p s' _ h1
    have e2 : planarRAMStep p (execI (sandboxTriple base T ONE exit s.pc (realStore a0 src)).1 s') = execI (sandboxTriple base T ONE exit s.pc (realStore a0 src)).2.1 (execI (sandboxTriple base T ONE exit s.pc (realStore a0 src)).1 s') :=
      step_eq p _ _ (by simpa [execI, sandboxTriple] using h2')
    have e3 : planarRAMStep p (execI (sandboxTriple base T ONE exit s.pc (realStore a0 src)).2.1 (execI (sandboxTriple base T ONE exit s.pc (realStore a0 src)).1 s')) =
        execI (sandboxTriple base T ONE exit s.pc (realStore a0 src)).2.2 (execI (sandboxTriple base T ONE exit s.pc (realStore a0 src)).2.1 (execI (sandboxTriple base T ONE exit s.pc (realStore a0 src)).1 s')) :=
      step_eq p _ _ (by simpa [execI, sandboxTriple] using h3')
    rw [run3, e1, e2, e3]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try rw [scratch_eq s'.natMem T ONE a0 (s.natMem a0) hOT hO' (hn a0)])
    all_goals (try simp only [Function.update_self])
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | natBranch l r y n =>
    refine ⟨1, by norm_num, ?_⟩
    rw [run1, step_eq p s' _ h1]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | realBranch l r y n =>
    refine ⟨1, by norm_num, ?_⟩
    rw [run1, step_eq p s' _ h1]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | jump j =>
    refine ⟨1, by norm_num, ?_⟩
    rw [run1, step_eq p s' _ h1]
    refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> dsimp only [execI, sandboxTriple]
    all_goals (try simp only [upd_relT _ T _ hTe, hn, hr])
    all_goals first
      | rfl
      | exact hO'
      | (rw [Function.update_of_ne (by omega)]; exact hO')
      | (rw [Function.update_of_ne (by omega), Function.update_of_ne hOT]; exact hO')
      | (rw [Function.update_of_ne hOT]; exact hO')
      | exact hn
      | exact hr
      | exact upd_rel _ _ _ _ hn
      | exact upd_rel _ _ _ _ hr
      | exact upd_rel _ _ _ _ (fun b => by rw [upd_relT _ T _ hTe, hn])
      | (intro a; rw [upd_relT _ T _ hTe, hn])
      | (intro a ha _; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha haT; rw [Function.update_of_ne (by omega), Function.update_of_ne haT])
      | (intro a ha haT; exact Function.update_of_ne haT _ _)
      | (intro a ha; exact Function.update_of_ne (by omega) _ _)
      | (intro a ha; rfl)
      | (intro a ha haT; rfl)
      | (split_ifs <;> rfl)
      | (intros; trivial)
      | omega
  | halt => exact absurd rfl hins

lemma run_add (p : List PlanarRAMInstruction) (s : PlanarRAMState) (a b : ℕ) :
    planarRAMRun p s (a + b) = planarRAMRun p (planarRAMRun p s a) b := by
  unfold planarRAMRun
  rw [add_comm, Function.iterate_add_apply]

lemma run_succ (p : List PlanarRAMInstruction) (s : PlanarRAMState) (t : ℕ) :
    planarRAMRun p s (t + 1) = planarRAMRun p (planarRAMStep p s) t := by
  unfold planarRAMRun
  rw [Function.iterate_succ_apply]

lemma step_none (p : List PlanarRAMInstruction) (s : PlanarRAMState) (h : p[s.pc]? = none) :
    planarRAMStep p s = s := by
  unfold planarRAMStep
  rw [h]

lemma run_fixed (p : List PlanarRAMInstruction) (s : PlanarRAMState)
    (h : planarRAMStep p s = s) (t : ℕ) : planarRAMRun p s t = s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, h, ih]

theorem sandbox_odd_simulation (p q : List PlanarRAMInstruction) (base T ONE exit : ℕ)
    (hTe : T % 2 = 0) (hOe : ONE % 2 = 0) (hTO : T ≠ ONE)
    (hp : SandboxedOddAt p q base T ONE exit) :
    ∀ (t : ℕ) (s s' : PlanarRAMState),
      q[(planarRAMRun q s t).pc]? = some PlanarRAMInstruction.halt →
      SandboxOddRel ONE s s' → s'.pc = base + 3 * s.pc →
      ∃ τ, τ ≤ 3 * t + 1 ∧
        (planarRAMRun p s' τ).pc = exit ∧
        SandboxOddRel ONE (planarRAMRun q s t) (planarRAMRun p s' τ) ∧
        (∀ a, a % 2 = 0 → a ≠ T → (planarRAMRun p s' τ).natMem a = s'.natMem a) ∧
        (∀ a, a % 2 = 0 → (planarRAMRun p s' τ).realMem a = s'.realMem a) := by
  intro t
  induction t with
  | zero =>
    intro s s' hhalt hrel hpc
    have hh : q[s.pc]? = some PlanarRAMInstruction.halt := hhalt
    obtain ⟨h1, -⟩ := hp s.pc _ hh
    rw [← hpc] at h1
    refine ⟨1, by omega, ?_⟩
    rw [run1, step_eq p s' _ h1]
    exact ⟨rfl, hrel, fun a _ _ => rfl, fun a _ => rfl⟩
  | succ t ih =>
    intro s s' hhalt hrel hpc
    rcases hq : q[s.pc]? with _ | ins
    · exfalso
      rw [run_fixed q s (step_none q s hq), hq] at hhalt
      exact absurd hhalt (by simp)
    · by_cases hins : ins = PlanarRAMInstruction.halt
      · subst hins
        have hfix : planarRAMStep q s = s := by rw [step_eq q s _ hq]; rfl
        rw [run_fixed q s hfix] at hhalt ⊢
        obtain ⟨h1, -⟩ := hp s.pc _ hq
        rw [← hpc] at h1
        refine ⟨1, by omega, ?_⟩
        rw [run1, step_eq p s' _ h1]
        exact ⟨rfl, hrel, fun a _ _ => rfl, fun a _ => rfl⟩
      · obtain ⟨τ₁, hτ₁, hpc₁, hrel₁, hfn₁, hfr₁⟩ :=
          sim_step p q base T ONE exit hTe hOe hTO hp s s' ins hq hins hrel hpc
        rw [run_succ] at hhalt ⊢
        obtain ⟨τ₂, hτ₂, hpc₂, hrel₂, hfn₂, hfr₂⟩ :=
          ih (planarRAMStep q s) (planarRAMRun p s' τ₁) hhalt hrel₁ hpc₁
        refine ⟨τ₁ + τ₂, by omega, ?_⟩
        rw [run_add]
        exact ⟨hpc₂, hrel₂, fun a ha haT => (hfn₂ a ha haT).trans (hfn₁ a ha haT),
          fun a ha => (hfr₂ a ha).trans (hfr₁ a ha)⟩

end SBO

open WilliamsonShmoys

theorem solution (p q : List PlanarRAMInstruction) (base T ONE exit : ℕ)
    (hTe : T % 2 = 0) (hOe : ONE % 2 = 0) (hTO : T ≠ ONE)
    (hp : SandboxedOddAt p q base T ONE exit) :
    ∀ (t : ℕ) (s s' : PlanarRAMState),
      q[(planarRAMRun q s t).pc]? = some PlanarRAMInstruction.halt →
      SandboxOddRel ONE s s' → s'.pc = base + 3 * s.pc →
      ∃ τ, τ ≤ 3 * t + 1 ∧
        (planarRAMRun p s' τ).pc = exit ∧
        SandboxOddRel ONE (planarRAMRun q s t) (planarRAMRun p s' τ) ∧
        (∀ a, a % 2 = 0 → a ≠ T → (planarRAMRun p s' τ).natMem a = s'.natMem a) ∧
        (∀ a, a % 2 = 0 → (planarRAMRun p s' τ).realMem a = s'.realMem a) :=
  SBO.sandbox_odd_simulation p q base T ONE exit hTe hOe hTO hp
