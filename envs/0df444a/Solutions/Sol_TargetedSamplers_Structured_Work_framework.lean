-- Prove2me | solution 1 for TargetedSamplers.Structured.Work.framework
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:02:49.188449+00:00
-- url     : https://prove2.me/submissions/2abb00a8-ce1b-446e-80be-5e13301e687f

import Definitions.Def_LogCostRAM_WorkExecution

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work

set_option autoImplicit false

namespace TargetedSamplers.Structured.WorkPf

@[simp] theorem compile_length (c : Cmd) (pc : ℕ) : (c.compile pc).length = c.len := by
  induction c generalizing pc <;> simp_all [Cmd.compile, Cmd.len] <;> omega

theorem exec_post {τ inv c s t k} (e : Exec τ inv c s t k) (hs : inv s) : inv t := by
  induction e <;> solve_by_elim

/-- A block embedded at absolute position `pc`. -/
def Contains (P : Program) (pc : ℕ) (code : Program) : Prop :=
  ∃ pre post : Program, pre.length = pc ∧ P = pre ++ code ++ post

theorem Contains.left {P pc x y} (h : Contains P pc (x++y)) : Contains P pc x := by
  obtain ⟨pre,post,hpc,hP⟩ := h
  exact ⟨pre, y++post, hpc, by simpa [List.append_assoc] using hP⟩

theorem Contains.right {P pc x y} (h : Contains P pc (x++y)) : Contains P (pc+x.length) y := by
  obtain ⟨pre,post,hpc,hP⟩ := h
  exact ⟨pre++x, post, by simp [hpc], by simpa [List.append_assoc] using hP⟩

theorem Contains.one {P pc i} (h : Contains P pc [i]) : P[pc]? = some i := by
  obtain ⟨pre,post,hpc,hP⟩ := h
  rw [hP, ← hpc, List.append_assoc, List.getElem?_append_right (by omega)]
  simp

structure Located (st : State) (pc : ℕ) (s : Store) : Prop where
  counter : st.pc = pc
  live : st.halted = false
  normal : st.bot = false
  memory : st.mem = s.mem
  output : st.out = s.out

theorem step_op {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]? = some p.instruction) : Located (P.step τ st) (pc+1) (p.eval τ s) := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  cases p <;> constructor <;>
    simp_all [Op.instruction, Op.eval, Program.step, State.write, Store.write]

theorem step_op_work {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]? = some p.instruction) :
    (P.step τ st).work = st.work + Op.cost τ s p := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  cases p <;> simp_all [Op.instruction, Op.cost, Program.step, State.write] <;> omega

theorem step_jle {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (a b dst : ℕ) (hp : P[pc]? = some (.jle a b dst)) :
    Located (P.step τ st) (if s.mem a ≤ s.mem b then dst else pc+1) s := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  constructor <;> simp [Program.step, hc, hh, hb, hm, ho, hp]

theorem step_jle_work {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (a b dst J : ℕ) (hp : P[pc]? = some (.jle a b dst)) (hd : dst.size ≤ J) :
    (P.step τ st).work ≤ st.work + jumpCost J s a b := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  simp [Program.step, hc, hh, hp, hm, jumpCost]
  omega

theorem step_jump {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (dst : ℕ) (hp : P[pc]? = some (jump dst)) : Located (P.step τ st) dst s := by
  simpa using step_jle τ h 0 0 dst hp

theorem branch_sites {P pc a b y n} (h : Contains P pc ((Cmd.branch a b y n).compile pc)) :
    P[pc]? = some (.jle a b (pc+1+n.len+1)) ∧ Contains P (pc+1) (n.compile (pc+1)) ∧
    P[pc+1+n.len]? = some (jump (pc+1+n.len+1+y.len)) ∧
    Contains P (pc+1+n.len+1) (y.compile (pc+1+n.len+1)) := by
  unfold Cmd.compile at h
  exact ⟨h.left.one, h.right.left, by simpa using h.right.right.left.one,
    by simpa using h.right.right.right⟩

theorem loop_sites {P pc a b body} (h : Contains P pc ((Cmd.whileGt a b body).compile pc)) :
    P[pc]? = some (.jle a b (pc+1+body.len+1)) ∧ Contains P (pc+1) (body.compile (pc+1)) ∧
    P[pc+1+body.len]? = some (jump pc) := by
  unfold Cmd.compile at h
  exact ⟨h.left.one, h.right.left, by simpa using h.right.right.one⟩

def Reaches (P : Program) (τ : Tapes) (st st' : State) : Prop := ∃ n, (P.step τ)^[n] st = st'

theorem Reaches.refl (P : Program) (τ : Tapes) (st : State) : Reaches P τ st st := ⟨0, rfl⟩

theorem Reaches.one (P : Program) (τ : Tapes) (st : State) : Reaches P τ st (P.step τ st) :=
  ⟨1, rfl⟩

theorem Reaches.trans {P τ a b c} (h : Reaches P τ a b) (h' : Reaches P τ b c) :
    Reaches P τ a c := by
  obtain ⟨n, rfl⟩ := h
  obtain ⟨m, rfl⟩ := h'
  exact ⟨m + n, Function.iterate_add_apply ..⟩

theorem wexec_compile {τ J c s t k} (ev : WExec τ J c s t k) (P : Program) (L : ℕ)
    (hL : L.size ≤ J) : ∀ (pc : ℕ) (st : State), Contains P pc (c.compile pc) →
    pc + c.len ≤ L → Located st pc s →
    ∃ t', Reaches P τ st t' ∧ Located t' (pc + c.len) t ∧ t'.work ≤ st.work + k := by
  have hsz : ∀ d, d ≤ L → d.size ≤ J := fun d hd => (Nat.size_le_size hd).trans hL
  induction ev with
  | skip s =>
    intro pc st _ _ hp
    exact ⟨st, .refl _ _ _, by simpa [Cmd.len] using hp, by simp⟩
  | op s p =>
    intro pc st hc _ hp
    exact ⟨_, .one _ _ _, by simpa [Cmd.len] using step_op τ hp p hc.one,
      (step_op_work τ hp p hc.one).le⟩
  | @seq x y s m t u v _ _ ix iy =>
    intro pc st hc hle hp
    simp only [Cmd.len] at hle
    obtain ⟨m1, r1, l1, w1⟩ := ix pc st hc.left (by omega) hp
    obtain ⟨m2, r2, l2, w2⟩ := iy (pc + x.len) m1 (by simpa using hc.right) (by omega) l1
    exact ⟨m2, r1.trans r2, by simpa [Cmd.len, Nat.add_assoc] using l2, by omega⟩
  | @yes a b y n s t k h _ iy =>
    intro pc st hc hle hp
    simp only [Cmd.len] at hle
    obtain ⟨ht,_,_,hy⟩ := branch_sites hc
    have hj := step_jle τ hp a b _ ht
    have hw := step_jle_work τ hp a b _ J ht (hsz _ (by omega))
    rw [if_pos h] at hj
    obtain ⟨out, r, l, w⟩ := iy _ _ hy (by omega) hj
    exact ⟨out, (Reaches.one _ _ _).trans r, by simpa [Cmd.len, Nat.add_assoc] using l,
      by omega⟩
  | @no a b y n s t k h _ ino =>
    intro pc st hc hle hp
    simp only [Cmd.len] at hle
    obtain ⟨ht,hn,hj,_⟩ := branch_sites hc
    have hs := step_jle τ hp a b _ ht
    have hw := step_jle_work τ hp a b _ J ht (hsz _ (by omega))
    rw [if_neg h] at hs
    obtain ⟨mid, r, l, w⟩ := ino _ _ hn (by omega) hs
    have hJump := step_jump τ l _ hj
    have hw2 := step_jle_work τ l 0 0 _ J hj (hsz _ (by omega))
    exact ⟨_, ((Reaches.one _ _ _).trans r).trans (.one _ _ _),
      by simpa [Cmd.len, Nat.add_assoc] using hJump, by omega⟩
  | @done a b body s h =>
    intro pc st hc hle hp
    simp only [Cmd.len] at hle
    have hj := step_jle τ hp a b _ (loop_sites hc).1
    have hw := step_jle_work τ hp a b _ J (loop_sites hc).1 (hsz _ (by omega))
    rw [if_pos h] at hj
    exact ⟨_, .one _ _ _, by simpa [Cmd.len, Nat.add_assoc] using hj, hw⟩
  | @again a b body s m t k j h _ _ ib il =>
    intro pc st hc hle hp
    have hle' := hle
    simp only [Cmd.len] at hle'
    obtain ⟨ht,hbody,hback⟩ := loop_sites hc
    have hs := step_jle τ hp a b _ ht
    have hw := step_jle_work τ hp a b _ J ht (hsz _ (by omega))
    rw [if_neg h] at hs
    obtain ⟨mid, r, l, w⟩ := ib _ _ hbody (by omega) hs
    have hret := step_jump τ l pc hback
    have hw2 := step_jle_work τ l 0 0 _ J hback (hsz _ (by omega))
    obtain ⟨out, r2, l2, w2⟩ := il pc _ hc hle hret
    exact ⟨out, (((Reaches.one _ _ _).trans r).trans (.one _ _ _)).trans r2, l2, by omega⟩
  | mono _ hk ih =>
    intro pc st hc hle hp
    obtain ⟨out, r, l, w⟩ := ih pc st hc hle hp
    exact ⟨out, r, l, by omega⟩

theorem final_eq_of_config_halted (P : Program) (τ : Tapes) (k : ℕ)
    (hh : (P.config τ k).halted = true) : P.final τ = some (P.config τ k) := by
  classical
  let h : ∃ j, (P.config τ j).halted = true := ⟨k, hh⟩
  have hmin := Nat.find_min' h hh
  have hhalt := Nat.find_spec h
  have hfix : P.step τ (P.config τ (Nat.find h)) = P.config τ (Nat.find h) := by
    simp [Program.step, hhalt]
  have hsame : P.config τ (k - Nat.find h + Nat.find h) = P.config τ (Nat.find h) := by
    exact (Function.iterate_add_apply ..).trans (Function.iterate_fixed hfix _)
  rw [Nat.sub_add_cancel hmin] at hsame
  rw [Program.final, dif_pos h, hsame]

/-- Conjunct 1. -/
theorem wexec_runsIn {τ : Tapes} {J : ℕ} {c : Cmd} {t : Store} {k : ℕ}
    (ev : WExec τ J c ⟨fun _ => 0, []⟩ t k) (hJ : ((c.compile 0).length).size ≤ J) :
    c.program.RunsIn τ (k + 1) (some t.out) := by
  let P := c.program
  have hloc : Located State.init 0 ⟨fun _ => 0, []⟩ := ⟨rfl,rfl,rfl,rfl,rfl⟩
  have hc : Contains P 0 (c.compile 0) := ⟨[],[.halt],rfl,rfl⟩
  rw [compile_length] at hJ
  obtain ⟨last, ⟨n, hn⟩, loc, hw⟩ := wexec_compile ev P c.len hJ 0 State.init hc (by omega) hloc
  have he : P.config τ n = last := hn
  have hpc : last.pc = (c.compile 0).length := by simpa using loc.counter
  have hhalt : P[last.pc]? = some .halt := by simp [hpc, P, Cmd.program]
  have hend : P.config τ (n+1) = {last with halted := true, work := last.work+1} := by
    change (P.step τ)^[n+1] State.init = _
    rw [Function.iterate_succ_apply']
    change P.step τ (P.config τ n) = _
    simp [he, Program.step, loc.live, hhalt]
  refine ⟨_, final_eq_of_config_halted P τ (n+1) (by rw [hend]), ?_, ?_⟩
  · rw [hend]
    simp [State.init] at hw
    simp
    omega
  · rw [hend]
    simp [State.result, loc.normal, loc.output]

theorem bitVal_size_le (u : Option Bool) : (bitVal u).size ≤ 2 := by
  cases u with
  | none => decide
  | some x => cases x <;> decide

theorem op_cost_le {τ : Tapes} {b J : ℕ} {s : Store} (p : Op) (hb : 2 ≤ b) (hs : s.Fits b)
    (hpost : (p.eval τ s).Fits b) (hF : ∀ x ∈ Op.fields p, x.size ≤ J) :
    Op.cost τ s p ≤ 4 * b + 4 * J + 4 := by
  cases p with
  | const d c =>
    simp [Op.fields] at hF
    simp [Op.cost]; omega
  | add d a c =>
    have h1 := hs a; have h2 := hs c; have h3 := hpost d
    simp [Op.eval, Store.write] at h3
    simp [Op.fields] at hF
    simp [Op.cost]; omega
  | sub d a c =>
    have h1 := hs a; have h2 := hs c; have h3 := hpost d
    simp [Op.eval, Store.write] at h3
    simp [Op.fields] at hF
    simp [Op.cost]; omega
  | load d a =>
    have h1 := hs a; have h2 := hs (s.mem a)
    simp [Op.fields] at hF
    simp [Op.cost]; omega
  | store a c =>
    have h1 := hs a; have h2 := hs c
    simp [Op.fields] at hF
    simp [Op.cost]; omega
  | input d a =>
    have h1 := hs a; have h2 := bitVal_size_le τ.input[s.mem a]?
    simp [Op.fields] at hF
    simp [Op.cost]; omega
  | coin d a =>
    have h1 := hs a; have h2 := bitVal_size_le τ.coins[s.mem a]?
    simp [Op.fields] at hF
    simp [Op.cost]; omega
  | output a =>
    have h1 := hs a
    simp [Op.fields] at hF
    simp [Op.cost]; omega

theorem jumpCost_le {J b : ℕ} {s : Store} {a c : ℕ} (hs : s.Fits b) (ha : a.size ≤ J)
    (hc : c.size ≤ J) : jumpCost J s a c ≤ 4 * b + 4 * J + 4 := by
  have h1 := hs a; have h2 := hs c
  simp [jumpCost]; omega

theorem jumpCost_zero_le {J b : ℕ} {s : Store} (hs : s.Fits b) :
    jumpCost J s 0 0 ≤ 4 * b + 4 * J + 4 := by
  have h1 := hs 0
  simp [jumpCost]; omega

/-- Conjunct 2. -/
theorem exec_to_wexec {τ : Tapes} {b J : ℕ} {c : Cmd} {s t : Store} {k : ℕ}
    (e : Exec τ (fun v => v.Fits b) c s t k) (hb : 2 ≤ b) :
    s.Fits b → Cmd.FieldsFit J c → WExec τ J c s t (k * (4 * b + 4 * J + 4)) := by
  induction e with
  | skip s => intro _ _; simpa using WExec.skip s
  | op s p hpost =>
    intro hs hF
    exact WExec.mono (.op s p) (by simpa using op_cost_le p hb hs hpost hF)
  | seq ex _ ix iy =>
    intro hs hF
    simp only [Cmd.FieldsFit] at hF
    rw [Nat.add_mul]
    exact WExec.seq (ix hs hF.1) (iy (exec_post ex hs) hF.2)
  | yes h _ iy =>
    intro hs hF
    simp only [Cmd.FieldsFit] at hF
    obtain ⟨ha, hc, hyF, _⟩ := hF
    have hj := jumpCost_le (b := b) hs ha hc
    refine WExec.mono (WExec.yes h (iy hs hyF)) ?_
    rw [Nat.add_mul, Nat.one_mul]; omega
  | no h en ino =>
    intro hs hF
    simp only [Cmd.FieldsFit] at hF
    obtain ⟨ha, hc, _, hnF⟩ := hF
    have hj := jumpCost_le (b := b) hs ha hc
    have hj2 := jumpCost_zero_le (J := J) (exec_post en hs)
    refine WExec.mono (WExec.no h (ino hs hnF)) ?_
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
  | done h =>
    intro hs hF
    simp only [Cmd.FieldsFit] at hF
    obtain ⟨ha, hc, _⟩ := hF
    exact WExec.mono (WExec.done h) (by simpa using jumpCost_le (b := b) hs ha hc)
  | again h eb _ ib il =>
    intro hs hF
    have hF' := hF
    simp only [Cmd.FieldsFit] at hF'
    obtain ⟨ha, hc, hbF⟩ := hF'
    have hj := jumpCost_le (b := b) hs ha hc
    have hm := exec_post eb hs
    have hj2 := jumpCost_zero_le (J := J) hm
    refine WExec.mono (WExec.again h (ib hs hbF) (il hm hF)) ?_
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega

theorem fieldsFit_of_compile (c : Cmd) : ∀ (pc W : ℕ),
    (∀ i ∈ c.compile pc, fieldWidth i ≤ W) → Cmd.FieldsFit W c := by
  induction c with
  | skip => intros; trivial
  | op p =>
    intro pc W h
    have h1 := h p.instruction (by simp [Cmd.compile])
    intro x hx
    cases p <;> simp [Op.fields] at hx <;> simp [Op.instruction, fieldWidth] at h1 <;>
      rcases hx with rfl | rfl | rfl <;> omega
  | seq x y ix iy =>
    intro pc W h
    exact ⟨ix pc W (fun i hi => h i (by simp [Cmd.compile, hi])),
      iy (pc + x.len) W (fun i hi => h i (by simp [Cmd.compile, hi]))⟩
  | branch a b y n iy ino =>
    intro pc W h
    have h1 := h (.jle a b (pc + 1 + n.len + 1)) (by simp [Cmd.compile])
    simp [fieldWidth] at h1
    exact ⟨h1.1, h1.2.1, iy (pc + 1 + n.len + 1) W (fun i hi => h i (by simp [Cmd.compile, hi])),
      ino (pc + 1) W (fun i hi => h i (by simp [Cmd.compile, hi]))⟩
  | whileGt a b body ib =>
    intro pc W h
    have h1 := h (.jle a b (pc + 1 + body.len + 1)) (by simp [Cmd.compile])
    simp [fieldWidth] at h1
    exact ⟨h1.1, h1.2.1, ib (pc + 1) W (fun i hi => h i (by simp [Cmd.compile, hi]))⟩

theorem fieldWidth_le_static {P : Program} {i : Instr} (h : i ∈ P) :
    fieldWidth i ≤ staticWidth P := by
  induction P with
  | nil => cases h
  | cons a p ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left ..
    · exact (ih h).trans (le_max_right ..)

/-- Conjunct 3. -/
theorem fieldsFit_static (c : Cmd) : Cmd.FieldsFit (staticWidth c.program) c :=
  fieldsFit_of_compile c 0 _ (fun i hi =>
    fieldWidth_le_static (by simp [Cmd.program, hi]))

/-- Conjunct 4. -/
theorem fieldsFit_mono {J J' : ℕ} (c : Cmd) (hJ : J ≤ J') (h : Cmd.FieldsFit J c) :
    Cmd.FieldsFit J' c := by
  induction c with
  | skip => trivial
  | op p => exact fun x hx => (h x hx).trans hJ
  | seq x y ix iy => exact ⟨ix h.1, iy h.2⟩
  | branch a b y n iy ino =>
    exact ⟨h.1.trans hJ, h.2.1.trans hJ, iy h.2.2.1, ino h.2.2.2⟩
  | whileGt a b body ib => exact ⟨h.1.trans hJ, h.2.1.trans hJ, ib h.2.2⟩

end TargetedSamplers.Structured.WorkPf

theorem solution :
    (∀ {τ : Tapes} {J : ℕ} {c : Cmd} {t : Store} {k : ℕ},
      WExec τ J c ⟨fun _ => 0, []⟩ t k → ((c.compile 0).length).size ≤ J →
      c.program.RunsIn τ (k + 1) (some t.out)) ∧
    (∀ {τ : Tapes} {b J : ℕ} {c : Cmd} {s t : Store} {k : ℕ},
      Exec τ (fun v => v.Fits b) c s t k → s.Fits b → Cmd.FieldsFit J c → 2 ≤ b →
      WExec τ J c s t (k * (4 * b + 4 * J + 4))) ∧
    (∀ (c : Cmd), Cmd.FieldsFit (staticWidth c.program) c) ∧
    (∀ {J J' : ℕ} (c : Cmd), J ≤ J' → Cmd.FieldsFit J c → Cmd.FieldsFit J' c) :=
  ⟨fun ev hJ => WorkPf.wexec_runsIn ev hJ,
   fun e hs hF hb => WorkPf.exec_to_wexec e hb hs hF,
   WorkPf.fieldsFit_static,
   fun c hJ h => WorkPf.fieldsFit_mono c hJ h⟩
