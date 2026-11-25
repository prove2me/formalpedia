-- Prove2me | solution 1 for PandoraKnapsack.Skipping.ArrayRAM.compile_cost_sound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:49:10.47402+00:00
-- url     : https://prove2.me/submissions/7969f4f8-5a19-4e77-9211-190dbbccf226

import Definitions.Def_PandoraKnapsack_Skipping_ArrayCompiler

namespace PandoraKnapsack.Skipping.StructuredRAM

@[simp] theorem Cmd.length_compile (c : Cmd) (base : ℕ) : (c.compile base).length = c.size := by
  induction c generalizing base <;> simp_all [Cmd.compile,Cmd.size] <;> omega

/-- Every instruction of a fragment occurs unchanged at its base offset in the whole program. -/
def Located (P : Program) (base : ℕ) (code : Program) :=
  ∀ i : ℕ, i < code.length → P[base+i]? = code[i]?

theorem Located.left {P a b : Program} {base : ℕ} (h : Located P base (a ++ b)) :
    Located P base a := by
  intro i hi
  rw [h i (by simp; omega), List.getElem?_append_left hi]

theorem Located.right {P a b : Program} {base : ℕ} (h : Located P base (a ++ b)) :
    Located P (base+a.length) b := by
  intro i hi
  rw [Nat.add_assoc, h (a.length+i) (by simp; omega), List.getElem?_append_right (by omega)]
  simp

theorem Located.single {P : Program} {base : ℕ} {ins : Instr} (h : Located P base [ins]) :
    P[base]? = some ins := by simpa using h 0 (by simp)

theorem Located.all (P : Program) : Located P 0 P := by intro i _; simp

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

private theorem step_of_prim {P : Program} {base : ℕ} {s : Store} {p : Prim}
    (h : P[base]? = some p.emit) :
    step I ω P (s.atPC base) = (p.exec I ω s).atPC (base+1) := by
  cases p <;> simp [step,Store.atPC,Prim.exec,Prim.emit,Store.setReg,Store.setPtr,
    SmaleNinth.RAMStep,coreProgram,List.getElem?_map,h] at h ⊢
  all_goals rfl

private theorem step_of_jump {P : Program} {base t : ℕ} {s : Store}
    (h : P[base]? = some (jump t)) : step I ω P (s.atPC base) = s.atPC t := by
  simp [step,Store.atPC,SmaleNinth.RAMStep,coreProgram,List.getElem?_map,h,jump]

private theorem step_of_guard {P : Program} {base r t : ℕ} {s : Store}
    (h : P[base]? = some (testLE r t)) :
    step I ω P (s.atPC base) = s.atPC (if s.regs r ≤ 0 then t else base+1) := by
  by_cases hr : s.regs r ≤ 0 <;>
    simp [step,Store.atPC,SmaleNinth.RAMStep,coreProgram,List.getElem?_map,h,testLE,hr]

private theorem step_of_accept {P : Program} {base : ℕ} {s : Store}
    (h : P[base]? = some (.core .accept)) : step I ω P (s.atPC base) = s.atPC base := by
  simp [step,Store.atPC,SmaleNinth.RAMStep,coreProgram,List.getElem?_map,h]

private theorem steps_then {α : Type*} {f : α → α} {a b c : α} {i j : ℕ}
    (hab : f^[i] a = b) (hbc : f^[j] b = c) : f^[i+j] a = c := by
  rw [Nat.add_comm,Function.iterate_add_apply,hab,hbc]

theorem Exec.simulate {c : Cmd} {s v : Store} {k : ℕ} (e : Exec I ω c s v k)
    {P : Program} {base : ℕ} (h : Located P base (c.compile base)) :
    (step I ω P)^[k] (s.atPC base) = v.atPC (base+c.size) := by
  induction e generalizing base with
  | skip => simp [Cmd.size]
  | prim => simpa [Cmd.size] using step_of_prim h.single
  | @seq a b s u v k l ea eb iha ihb =>
    have he := steps_then (iha h.left) (ihb (by simpa using h.right))
    simpa [Cmd.size,Nat.add_assoc] using he
  | @ite_true r a b s v k hr ea iha =>
    change Located P base ([testLE r _] ++ (a.compile _ ++ ([jump _] ++ b.compile _))) at h
    have ha := h.right
    simp only [List.length_singleton] at ha
    have hj := ha.right
    simp only [Cmd.length_compile] at hj
    have hg := @step_of_guard _ _ _ I ω _ _ _ _ s h.left.single
    rw [if_neg hr.not_ge] at hg
    have he := steps_then (steps_then (show (step I ω P)^[1] (s.atPC base) = _ from hg) (iha ha.left))
      (show (step I ω P)^[1] _ = _ from step_of_jump hj.left.single)
    simpa [Cmd.size,Nat.add_assoc] using he
  | @ite_false r a b s v k hr eb ihb =>
    change Located P base ([testLE r _] ++ (a.compile _ ++ ([jump _] ++ b.compile _))) at h
    have hb := h.right.right.right
    simp only [List.length_singleton,Cmd.length_compile] at hb
    have hg := @step_of_guard _ _ _ I ω _ _ _ _ s h.left.single
    rw [if_pos hr] at hg
    have he := steps_then (show (step I ω P)^[1] (s.atPC base) = _ from hg) (ihb hb)
    simpa [Cmd.size,Nat.add_assoc] using he
  | @while_false r a s hr =>
    change Located P base ([testLE r _] ++ (a.compile _ ++ [jump _])) at h
    have hg := @step_of_guard _ _ _ I ω _ _ _ _ s h.left.single
    simpa [Cmd.size,hr,Nat.add_assoc] using hg
  | @while_true r a s u v k l hr ea eloop iha ihloop =>
    change Located P base ([testLE r _] ++ (a.compile _ ++ [jump _])) at h
    have ha := h.right
    simp only [List.length_singleton] at ha
    have hj := ha.right
    simp only [Cmd.length_compile] at hj
    have hg := @step_of_guard _ _ _ I ω _ _ _ _ s h.left.single
    rw [if_neg hr.not_ge] at hg
    exact steps_then (steps_then (steps_then
      (show (step I ω P)^[1] (s.atPC base) = _ from hg) (iha ha.left))
      (show (step I ω P)^[1] _ = _ from step_of_jump hj.single)) (ihloop h)

theorem Exec.run_eq {c : Cmd} {v : Store} {k B : ℕ}
    (e : Exec I ω c (initial n m T) v k) (hB : k ≤ B) :
    run I ω (program c) B = v.atPC c.size := by
  have hall := Located.all (program c)
  have hf := e.simulate hall.left
  have hacc := hall.right.single
  simp only [Cmd.length_compile,Nat.zero_add] at hf hacc
  have hfix : step I ω (program c) (v.atPC c.size) = v.atPC c.size := step_of_accept hacc
  have hs : (step I ω (program c))^[B-k] (v.atPC c.size) = v.atPC c.size := Function.iterate_fixed hfix _
  have he := steps_then hf hs
  rwa [Nat.add_sub_of_le hB] at he

theorem Exec.halted {c : Cmd} {v : Store} {k B : ℕ} (e : Exec I ω c (initial n m T) v k)
    (hB : k ≤ B) : Halted (program c) (run I ω (program c) B) := by
  rw [e.run_eq hB]
  have h := (Located.all (program c)).right.single
  simpa [Halted,Store.atPC] using h

end PandoraKnapsack.Skipping.StructuredRAM

namespace PandoraKnapsack.Skipping.StructuredRAM

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

theorem exec_gap (q addr tmp : ℕ) (hne : addr ≠ tmp) (s : Store) :
    Exec I ω (gap q addr tmp) s (s.setReg tmp (s.regs addr - (s.ptrs q : ℝ))) 2 := by
  have e := Exec.seq (Exec.prim (I := I) (ω := ω) s (.ptrReal tmp q)) (Exec.prim _ (.sub tmp addr tmp))
  simpa [gap,Prim.exec,Store.setReg,hne,Function.update_of_ne,Function.update_idem] using e

private theorem exec_seek_loop (q addr tmp : ℕ) (hne : addr ≠ tmp) (s : Store) (start left : ℕ)
    (haddr : s.regs addr = ↑(start+left)) :
    Exec I ω (.whilePos tmp (.seq (.prim (.pinc q)) (gap q addr tmp)))
      ((s.setPtr q start).setReg tmp left) ((s.setPtr q (start+left : ℕ)).setReg tmp 0)
      (5*left+1) := by
  induction left generalizing start with
  | zero =>
    simp only [Nat.add_zero,Nat.cast_zero,Nat.mul_zero,Nat.zero_add]
    apply Exec.while_false
    simp [Store.setReg]
  | succ left ih =>
    let u := (s.setPtr q start).setReg tmp (left.succ : ℝ)
    let v := (s.setPtr q (start+1 : ℕ)).setReg tmp (left : ℝ)
    have eg : 0 < u.regs tmp := by simp [u,Store.setReg]; positivity
    have next : Exec I ω (.seq (.prim (.pinc q)) (gap q addr tmp)) u v 3 := by
      have e := Exec.seq (Exec.prim (I := I) (ω := ω) u (.pinc q)) (exec_gap q addr tmp hne _)
      have hcalc : s.regs addr - ((start : ℝ)+1) = (left : ℝ) := by push_cast at haddr; linarith
      simpa [u,v,Prim.exec,Store.setReg,Store.setPtr,hne,Function.update_of_ne,
        Function.update_idem,Nat.cast_add_one,hcalc] using e
    have et := ih (start+1) (by rw [haddr]; congr 1; omega)
    have e := Exec.while_true eg next et
    have hi : start+1+left = start+left.succ := by omega
    have hc : 1+3+1+(5*left+1) = 5*left.succ+1 := by omega
    simpa only [hi,hc,u,v] using e

theorem exec_seek (q addr tmp k : ℕ) (hne : addr ≠ tmp) (s : Store) (ha : s.regs addr = k) :
    Exec I ω (seek q addr tmp) s ((s.setPtr q k).setReg tmp 0) (5*k+4) := by
  have ew := exec_seek_loop (I := I) (ω := ω) q addr tmp hne s 0 k (by simpa using ha)
  simp only [Nat.zero_add,Nat.cast_zero] at ew
  have e0 := Exec.prim (I := I) (ω := ω) s (.pset q 0)
  have e1 : Exec I ω (gap q addr tmp) (Prim.exec I ω s (.pset q 0))
      ((s.setPtr q 0).setReg tmp (k : ℝ)) 2 := by
    simpa [Prim.exec,Store.setPtr,ha] using exec_gap (I := I) (ω := ω) q addr tmp hne (s.setPtr q 0)
  have hc : 1+(2+(5*k+1)) = 5*k+4 := by omega
  simpa only [seek,hc] using Exec.seq e0 (Exec.seq e1 ew)

theorem exec_readAt (dst addr q tmp k : ℕ) (hne : addr ≠ tmp) (s : Store)
    (ha : s.regs addr = k) :
    Exec I ω (readAt dst addr q tmp) s (((s.setPtr q k).setReg tmp 0).setReg dst (s.mem k)) (5*k+5) := by
  have e := Exec.seq (exec_seek (I := I) (ω := ω) q addr tmp k hne s ha) (Exec.prim _ (.load dst q))
  simpa [readAt,Prim.exec,Store.setReg,Store.setPtr] using e

theorem exec_writeAt (addr src q tmp k : ℕ) (hne : addr ≠ tmp) (hs : src ≠ tmp) (s : Store)
    (ha : s.regs addr = k) :
    Exec I ω (writeAt addr src q tmp) s
      { (s.setPtr q k).setReg tmp 0 with mem := Function.update s.mem k (s.regs src) } (5*k+5) := by
  have e := Exec.seq (exec_seek (I := I) (ω := ω) q addr tmp k hne s ha) (Exec.prim _ (.store q src))
  simpa [writeAt,Prim.exec,Store.setReg,Store.setPtr,hs,Function.update_of_ne] using e

end PandoraKnapsack.Skipping.StructuredRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
open StructuredRAM (Prim Cmd)
local notation "SStore" => StructuredRAM.Store
local notation "SExec" => StructuredRAM.Exec

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

theorem exec_negGap (q addr tmp : ℕ) (hne : addr ≠ tmp) (s : SStore) :
    SExec I ω (negGap q addr tmp) s (s.setReg tmp (s.regs addr + (s.ptrs q : ℝ))) 2 := by
  have e := StructuredRAM.Exec.seq (StructuredRAM.Exec.prim (I := I) (ω := ω) s (.ptrReal tmp q)) (StructuredRAM.Exec.prim _ (.add tmp addr tmp))
  simpa [negGap,ins,Prim.exec,StructuredRAM.Store.setReg,hne,Function.update_of_ne,Function.update_idem] using e

private theorem exec_negSeek_loop (q addr tmp : ℕ) (hne : addr ≠ tmp) (s : SStore) (start left : ℕ)
    (haddr : s.regs addr = ↑(start+left)) :
    SExec I ω (.whilePos tmp (.seq (.prim (.pdec q)) (negGap q addr tmp)))
      ((s.setPtr q (-(start:ℤ))).setReg tmp left) ((s.setPtr q (-(start+left : ℕ) : ℤ)).setReg tmp 0)
      (5*left+1) := by
  induction left generalizing start with
  | zero =>
    simp only [Nat.add_zero,Nat.cast_zero,Nat.mul_zero,Nat.zero_add]
    apply StructuredRAM.Exec.while_false
    simp [StructuredRAM.Store.setReg]
  | succ left ih =>
    let u : SStore := (s.setPtr q (-(start:ℤ))).setReg tmp (left.succ : ℝ)
    let v : SStore := (s.setPtr q (-(start+1 : ℕ) : ℤ)).setReg tmp (left : ℝ)
    have eg : 0 < u.regs tmp := by simp [u,StructuredRAM.Store.setReg]; positivity
    have next : SExec I ω (.seq (.prim (.pdec q)) (negGap q addr tmp)) u v 3 := by
      have e := StructuredRAM.Exec.seq (StructuredRAM.Exec.prim (I := I) (ω := ω) u (.pdec q)) (exec_negGap q addr tmp hne _)
      have hcalc : s.regs addr + (-1 + -(start : ℝ)) = (left : ℝ) := by push_cast at haddr; linarith
      have hp : (-(start:ℤ)-1) = -1 + -(start:ℤ) := by omega
      simpa [u,v,Prim.exec,StructuredRAM.Store.setReg,StructuredRAM.Store.setPtr,hne,Function.update_of_ne,
        Function.update_idem,Nat.cast_add_one,hcalc,hp] using e
    have et := ih (start+1) (by rw [haddr]; congr 1; omega)
    have e := StructuredRAM.Exec.while_true eg next et
    have hi : start+1+left = start+left.succ := by omega
    have hc : 1+3+1+(5*left+1) = 5*left.succ+1 := by omega
    simpa only [hi,hc,u,v] using e

theorem exec_negSeek (q addr tmp k : ℕ) (hne : addr ≠ tmp) (s : SStore) (ha : s.regs addr = k) :
    SExec I ω (negSeek q addr tmp) s ((s.setPtr q (-(k:ℤ))).setReg tmp 0) (5*k+4) := by
  have ew := exec_negSeek_loop (I := I) (ω := ω) q addr tmp hne s 0 k (by simpa using ha)
  simp only [Nat.zero_add,Nat.cast_zero,Int.neg_zero] at ew
  have e0 := StructuredRAM.Exec.prim (I := I) (ω := ω) s (.pset q 0)
  have e1 : SExec I ω (negGap q addr tmp) (Prim.exec I ω s (.pset q 0))
      ((s.setPtr q 0).setReg tmp (k : ℝ)) 2 := by
    simpa [Prim.exec,StructuredRAM.Store.setPtr,ha] using exec_negGap (I := I) (ω := ω) q addr tmp hne (s.setPtr q 0)
  have hc : 1+(2+(5*k+1)) = 5*k+4 := by omega
  simpa only [negSeek,ins,hc] using StructuredRAM.Exec.seq e0 (StructuredRAM.Exec.seq e1 ew)

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM

open StructuredRAM (Cmd Prim)
local notation "S" => StructuredRAM.Store
local notation "E" => StructuredRAM.Exec

/-- Representation invariant at every source-language command boundary. -/
structure Rep (a : Store) (s : S) : Prop where
  natReg (j : ℕ) : s.regs (nr j) = (a.ns j : ℝ)
  realReg (j : ℕ) : s.regs (rr j) = a.rs j
  zeroReg : s.regs 3 = 0
  oneReg : s.regs 7 = 1
  table (t : Fin 16) (j : ℕ) : s.mem (-(tableOffset t j : ℤ)) = a.tab t j
  output (j : ℕ) : s.mem j = a.out j
  draws : s.draws = a.draws

def Low (d : ℕ) (s v : S) := ∀ j < d, v.regs (tr j) = s.regs (tr j)
structure RegisterFrame (d : ℕ) (s v : S) : Prop where
  low : Low d s v
  ptrs : ∀ j < 2, v.ptrs j = s.ptrs j

theorem RegisterFrame.refl (d : ℕ) (s : S) : RegisterFrame d s s := ⟨fun _ _ => rfl,fun _ _ => rfl⟩
theorem RegisterFrame.trans {d : ℕ} {s u v : S} (h : RegisterFrame d s u) (h' : RegisterFrame d u v) : RegisterFrame d s v :=
  ⟨fun i hi => (h'.low i hi).trans (h.low i hi),fun i hi => (h'.ptrs i hi).trans (h.ptrs i hi)⟩
theorem RegisterFrame.weaken {d e : ℕ} {s v : S} (h : RegisterFrame e s v) (hle : d ≤ e) : RegisterFrame d s v :=
  ⟨fun i hi => h.low i (by omega), h.ptrs⟩

theorem Rep.writeTmp {a : Store} {s : S} (h : Rep a s) (d : ℕ) (v : ℝ) : Rep a (s.setReg (tr d) v) := by
  refine ⟨?_,?_,?_,?_,h.table,h.output,h.draws⟩
  · intro j; simpa [StructuredRAM.Store.setReg,Function.update_of_ne (show nr j ≠ tr d by unfold nr tr; omega)] using h.natReg j
  · intro j; simpa [StructuredRAM.Store.setReg,Function.update_of_ne (show rr j ≠ tr d by unfold rr tr; omega)] using h.realReg j
  · simpa [StructuredRAM.Store.setReg,Function.update_of_ne (show 3 ≠ tr d by unfold tr; omega)] using h.zeroReg
  · simpa [StructuredRAM.Store.setReg,Function.update_of_ne (show 7 ≠ tr d by unfold tr; omega)] using h.oneReg

theorem Rep.setPtr {a : Store} {s : S} (h : Rep a s) (q : ℕ) (v : ℤ) : Rep a (s.setPtr q v) :=
  ⟨h.natReg,h.realReg,h.zeroReg,h.oneReg,h.table,h.output,h.draws⟩

theorem frame_tmp (s : S) (d e : ℕ) (v : ℝ) (h : d ≤ e) : RegisterFrame d s (s.setReg (tr e) v) := by
  refine ⟨?_, fun _ _ => rfl⟩
  intro i hi
  exact Function.update_of_ne (by unfold tr; omega) _ _

theorem frame_tablePtr (s : S) (d : ℕ) (v : ℤ) : RegisterFrame d s (s.setPtr 2 v) :=
  ⟨fun _ _ => rfl,fun j hj => Function.update_of_ne (by omega) _ _⟩

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

def EvalRun (I : Instance n m T) (ω : ℕ → ℝ) (a : Store) (s : S) (d : ℕ) (c : Cmd) (val : ℝ) (k : ℕ) :=
  ∃ u, E I ω c s u k ∧ Rep a u ∧ RegisterFrame d s u ∧ u.regs (tr d) = val

theorem eval_prim {a : Store} {s : S} {d : ℕ} {v : ℝ} {p : Prim} (hs : Rep a s)
    (hp : p.exec I ω s = s.setReg (tr d) v) : EvalRun I ω a s d (ins p) v 1 := by
  refine ⟨_, hp ▸ StructuredRAM.Exec.prim s p, hs.writeTmp d v, frame_tmp s d d v le_rfl, ?_⟩
  simp [StructuredRAM.Store.setReg]

private theorem join_bin {a : Store} {s : S} {d ka kb : ℕ} {ca cb : Cmd} {p : Prim}
    {va vb v : ℝ} (ha : EvalRun I ω a s d ca va ka)
    (hb : ∀ u, Rep a u → EvalRun I ω a u (d+1) cb vb kb)
    (hp : ∀ w : S, w.regs (tr d) = va → w.regs (tr (d+1)) = vb → p.exec I ω w = w.setReg (tr d) v) :
    EvalRun I ω a s d (block [ca,cb,ins p]) v (ka+kb+1) := by
  obtain ⟨u,eu,hu,fu,vu⟩ := ha
  obtain ⟨w,ew,hw,fw,vw⟩ := hb u hu
  obtain ⟨z,ez,hz,fz,vz⟩ := eval_prim hw (hp w ((fw.low d (by omega)).trans vu) vw)
  refine ⟨z,?_,hz,(fu.trans (fw.weaken (by omega))).trans fz,vz⟩
  simpa [block,Nat.add_assoc] using StructuredRAM.Exec.seq eu (StructuredRAM.Exec.seq ew
    (StructuredRAM.Exec.seq ez (StructuredRAM.Exec.skip z)))

theorem lower_nat (e : N) (d : ℕ) {a : Store} {s : S} (hs : Rep a s) :
    EvalRun I ω a s d (e.lower d) (e.eval a : ℝ) e.work := by
  induction e generalizing d s with
  | lit k => exact eval_prim hs rfl
  | var j =>
    apply eval_prim hs
    simp [N.eval,Prim.exec,hs.zeroReg,hs.natReg]
  | add x y ix iy =>
    apply join_bin (ix d hs) (fun u hu => iy (d+1) hu)
    intro w hw hy
    simp [Prim.exec,hw,hy,N.eval]
  | mul x y ix iy =>
    apply join_bin (ix d hs) (fun u hu => iy (d+1) hu)
    intro w hw hy
    simp [Prim.exec,hw,hy,N.eval]

/-- Appending one arithmetic operation to a verified expression. -/
private theorem eval_append {a : Store} {s : S} {d k : ℕ} {c : Cmd} {p : Prim} {v v' : ℝ}
    (h : EvalRun I ω a s d c v k)
    (hp : ∀ u, u.regs (tr d) = v → p.exec I ω u = u.setReg (tr d) v') :
    EvalRun I ω a s d (.seq c (ins p)) v' (k+1) := by
  obtain ⟨u,eu,hu,fu,vu⟩ := h
  obtain ⟨w,ew,hw,fw,vw⟩ := eval_prim hu (hp u vu)
  exact ⟨w,StructuredRAM.Exec.seq eu ew,hw,fu.trans fw,vw⟩

theorem lower_tableAddress (d : ℕ) (t : Fin 16) (i : N) {a : Store} {s : S} (hs : Rep a s) :
    EvalRun I ω a s d (tableAddress d t i) (tableOffset t (i.eval a) : ℝ) (i.work+4) := by
  obtain ⟨u,eu,hu,fu,vu⟩ := lower_nat (I := I) (ω := ω) i d hs
  let v := u.setReg (tr (d+1)) 16
  let w := v.setReg (tr d) (16*(i.eval a : ℝ))
  let z := w.setReg (tr (d+1)) ((t.val+1 : ℕ) : ℝ)
  let o := z.setReg (tr d) (tableOffset t (i.eval a) : ℝ)
  have hd : tr d ≠ tr (d+1) := by unfold tr; omega
  have e1 : E I ω (ins (.const (tr (d+1)) 16)) u v 1 := StructuredRAM.Exec.prim _ _
  have e2 : E I ω (ins (.mul (tr d) (tr d) (tr (d+1)))) v w 1 := by
    simpa [ins,Prim.exec,v,w,StructuredRAM.Store.setReg,Function.update_of_ne hd,vu,mul_comm] using
      StructuredRAM.Exec.prim (I := I) (ω := ω) v (.mul (tr d) (tr d) (tr (d+1)))
  have e3 : E I ω (ins (.const (tr (d+1)) (t.val+1 : ℕ))) w z 1 := StructuredRAM.Exec.prim _ _
  have e4 : E I ω (ins (.add (tr d) (tr d) (tr (d+1)))) z o 1 := by
    have hval : (16*(i.eval a : ℝ))+((t.val : ℝ)+1) = (tableOffset t (i.eval a) : ℝ) := by
      push_cast [tableOffset]; ring
    simpa [ins,o,z,w,Prim.exec,StructuredRAM.Store.setReg,Function.update_of_ne hd,hval] using
      StructuredRAM.Exec.prim (I := I) (ω := ω) z (.add (tr d) (tr d) (tr (d+1)))
  refine ⟨o,?_,(((hu.writeTmp _ _).writeTmp _ _).writeTmp _ _).writeTmp _ _,?_, by simp [o,StructuredRAM.Store.setReg]⟩
  · simpa [tableAddress,block,Nat.add_assoc] using StructuredRAM.Exec.seq eu (StructuredRAM.Exec.seq e1
      (StructuredRAM.Exec.seq e2 (StructuredRAM.Exec.seq e3 (StructuredRAM.Exec.seq e4 (StructuredRAM.Exec.skip o)))))
  · exact (((fu.trans (frame_tmp _ _ _ _ (by omega))).trans (frame_tmp _ _ _ _ le_rfl)).trans
      (frame_tmp _ _ _ _ (by omega))).trans (frame_tmp _ _ _ _ le_rfl)

theorem lower_real (e : R) (d : ℕ) {a : Store} {s : S} (hs : Rep a s) :
    EvalRun I ω a s d (e.lower d) (e.eval a) (e.work a) := by
  induction e generalizing d s with
  | lit v => exact eval_prim hs rfl
  | var j =>
    apply eval_prim hs
    simp [R.eval,Prim.exec,hs.zeroReg,hs.realReg]
  | nat i => exact lower_nat i d hs
  | get t i =>
    obtain ⟨u,eu,hu,fu,vu⟩ := lower_tableAddress (I := I) (ω := ω) d t i hs
    let off := tableOffset t (i.eval a)
    let w := (u.setPtr 2 (-(off : ℤ))).setReg (tr (d+1)) 0
    have en : E I ω (negSeek 2 (tr d) (tr (d+1))) u w (5*off+4) :=
      exec_negSeek _ _ _ off (by unfold tr; omega) _ vu
    let v := w.setReg (tr d) (a.tab t (i.eval a))
    have ev : E I ω (ins (.load (tr d) 2)) w v 1 := by
      simpa [ins,v,w,off,Prim.exec,StructuredRAM.Store.setReg,StructuredRAM.Store.setPtr,hu.table] using
        StructuredRAM.Exec.prim (I := I) (ω := ω) w (.load (tr d) 2)
    refine ⟨v,?_,((hu.setPtr _ _).writeTmp _ _).writeTmp _ _,?_,by simp [v,StructuredRAM.Store.setReg,R.eval]⟩
    · simpa [R.lower,R.work,readTable,off,Nat.add_assoc] using
        StructuredRAM.Exec.seq eu (StructuredRAM.Exec.seq en ev)
    · exact ((fu.trans (frame_tablePtr _ _ _)).trans (frame_tmp _ _ _ _ (by omega))).trans (frame_tmp _ _ _ _ le_rfl)
  | add x y ix iy | sub x y ix iy | mul x y ix iy | div x y ix iy =>
    apply join_bin (ix d hs) (fun u hu => iy (d+1) hu)
    intro w hx hy
    simp [Prim.exec,hx,hy,R.eval]

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
open StructuredRAM (Cmd Prim)
local notation "S" => StructuredRAM.Store
local notation "E" => StructuredRAM.Exec

theorem Low.refl (d : ℕ) (s : S) : Low d s s := fun _ _ => rfl
theorem Low.trans {d : ℕ} {s u v : S} (h : Low d s u) (h' : Low d u v) : Low d s v :=
  fun j hj => (h' j hj).trans (h j hj)
theorem Low.weaken {d e : ℕ} {s v : S} (h : Low e s v) (hle : d ≤ e) : Low d s v :=
  fun j hj => h j (by omega)

theorem Rep.setN {a : Store} {s : S} (h : Rep a s) (r k : ℕ) : Rep (a.setN r k) (s.setReg (nr r) k) := by
  refine ⟨?_,?_,?_,?_,h.table,h.output,h.draws⟩
  · intro j; by_cases hj : j = r
    · subst j; simp [Store.setN,StructuredRAM.Store.setReg]
    · simp [Store.setN,StructuredRAM.Store.setReg,Function.update_of_ne hj, h.natReg,
        Function.update_of_ne (show nr j ≠ nr r by unfold nr; omega)]
  · intro j; simpa [Store.setN,StructuredRAM.Store.setReg,Function.update_of_ne (show rr j ≠ nr r by unfold rr nr; omega)] using h.realReg j
  · simpa [StructuredRAM.Store.setReg,Function.update_of_ne (show 3 ≠ nr r by unfold nr; omega)] using h.zeroReg
  · simpa [StructuredRAM.Store.setReg,Function.update_of_ne (show 7 ≠ nr r by unfold nr; omega)] using h.oneReg

theorem Rep.setR {a : Store} {s : S} (h : Rep a s) (r : ℕ) (k : ℝ) : Rep (a.setR r k) (s.setReg (rr r) k) := by
  refine ⟨?_,?_,?_,?_,h.table,h.output,h.draws⟩
  · intro j; simpa [Store.setR,StructuredRAM.Store.setReg,Function.update_of_ne (show nr j ≠ rr r by unfold nr rr; omega)] using h.natReg j
  · intro j; by_cases hj : j = r
    · subst j; simp [Store.setR,StructuredRAM.Store.setReg]
    · simp [Store.setR,StructuredRAM.Store.setReg,Function.update_of_ne hj, h.realReg,
        Function.update_of_ne (show rr j ≠ rr r by unfold rr; omega)]
  · simpa [StructuredRAM.Store.setReg,Function.update_of_ne (show 3 ≠ rr r by unfold rr; omega)] using h.zeroReg
  · simpa [StructuredRAM.Store.setReg,Function.update_of_ne (show 7 ≠ rr r by unfold rr; omega)] using h.oneReg

theorem low_setN (d : ℕ) (s : S) (r : ℕ) (k : ℝ) : Low d s (s.setReg (nr r) k) :=
  fun j _ => Function.update_of_ne (by unfold tr nr; omega) _ _
theorem low_setR (d : ℕ) (s : S) (r : ℕ) (k : ℝ) : Low d s (s.setReg (rr r) k) :=
  fun j _ => Function.update_of_ne (by unfold tr rr; omega) _ _

private lemma off_pos (t : Fin 16) (i : ℕ) : 0 < tableOffset t i := by unfold tableOffset; omega
private lemma off_inj {u v : Fin 16} {i j : ℕ} (h : tableOffset u i = tableOffset v j) : u = v ∧ i = j := by
  unfold tableOffset at h
  constructor
  · apply Fin.ext; omega
  · omega

theorem Rep.put {a : Store} {s : S} (h : Rep a s) (t : Fin 16) (i : ℕ) (v : ℝ) :
    Rep (a.put t i v) {s with mem := Function.update s.mem (-(tableOffset t i : ℤ)) v} := by
  refine ⟨h.natReg,h.realReg,h.zeroReg,h.oneReg,?_,?_,h.draws⟩
  · intro u j
    by_cases hu : u = t
    · subst u
      by_cases hj : j = i
      · subst j; simp [Store.put]
      · have hne : -(tableOffset t j : ℤ) ≠ -(tableOffset t i : ℤ) := by
          intro he; exact hj (off_inj (u:=t) (v:=t) (by omega)).2
        simp [Store.put,Function.update_of_ne hj,Function.update_of_ne hne,h.table]
    · have hne : -(tableOffset u j : ℤ) ≠ -(tableOffset t i : ℤ) := by
        intro he; exact hu (off_inj (i:=j) (j:=i) (by omega)).1
      simp [Store.put,Function.update_of_ne hu,Function.update_of_ne hne,h.table]
  · intro j
    exact (Function.update_of_ne (by have := off_pos t i; omega) _ _).trans (h.output j)

theorem Rep.writeOut {a : Store} {s : S} (h : Rep a s) (i : ℕ) (v : ℝ) :
    Rep (a.writeOut i v) {s with mem := Function.update s.mem (i : ℤ) v} := by
  refine ⟨h.natReg,h.realReg,h.zeroReg,h.oneReg,?_,?_,h.draws⟩
  · intro t j
    exact (Function.update_of_ne (by have := off_pos t j; omega) _ _).trans (h.table t j)
  · intro j; by_cases hj : j = i
    · subst j; simp [Store.writeOut]
    · simp [Store.writeOut,Function.update_of_ne hj,h.output,Function.update_of_ne (show (j : ℤ) ≠ i by omega)]

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

def CmdRun (I : Instance n m T) (ω : ℕ → ℝ) (a : Store) (s : S) (d : ℕ) (c : Cmd) (k : ℕ) :=
  ∃ u, E I ω c s u k ∧ Rep a u ∧ Low d s u

theorem lower_setIndex (d q : ℕ) (i : N) {a : Store} {s : S} (hs : Rep a s) :
    ∃ v, E I ω (setIndex d q i) s v (indexWork a i) ∧ Rep a v ∧ Low d s v ∧
      v.ptrs q = (i.eval a : ℤ) ∧ ∀ j < 2, j ≠ q → v.ptrs j = s.ptrs j := by
  obtain ⟨u,eu,hu,fu,vu⟩ := lower_nat (I := I) (ω := ω) i d hs
  have es := StructuredRAM.exec_seek (I := I) (ω := ω) q (tr d) (tr (d+1))
    (i.eval a) (by unfold tr; omega) u vu
  refine ⟨_,StructuredRAM.Exec.seq eu es,(hu.setPtr _ _).writeTmp _ _,?_,by simp [StructuredRAM.Store.setPtr,StructuredRAM.Store.setReg],?_⟩
  · exact fu.low.trans (fun j hj => Function.update_of_ne (show tr j ≠ tr (d+1) by unfold tr; omega) _ _)
  · intro j hj hq
    exact (Function.update_of_ne hq _ _).trans (fu.ptrs j hj)

theorem lower_put (d : ℕ) (t : Fin 16) (i : N) (e : R) {a : Store} {s : S} (hs : Rep a s) :
    CmdRun I ω (a.put t (i.eval a) (e.eval a)) s d ((C.put t i e).lower d)
      (i.work+4+e.work a+(5*tableOffset t (i.eval a)+5)) := by
  obtain ⟨u,eu,hu,fu,vu⟩ := lower_tableAddress (I := I) (ω := ω) d t i hs
  obtain ⟨w,ew,hw,fw,vw⟩ := lower_real (I := I) (ω := ω) e (d+1) hu
  let off := tableOffset t (i.eval a)
  let v := (w.setPtr 2 (-(off : ℤ))).setReg (tr (d+2)) 0
  have en : E I ω (negSeek 2 (tr d) (tr (d+2))) w v (5*off+4) :=
    exec_negSeek _ _ _ off (by unfold tr; omega) _ ((fw.low d (by omega)).trans vu)
  let out := {v with mem := Function.update v.mem (-(off : ℤ)) (e.eval a)}
  have es : E I ω (ins (.store 2 (tr (d+1)))) v out 1 := by
    have hn : tr (d+1) ≠ tr (d+2) := by unfold tr; omega
    simpa [ins,out,v,Prim.exec,StructuredRAM.Store.setReg,StructuredRAM.Store.setPtr,Function.update_of_ne hn,vw] using
      StructuredRAM.Exec.prim (I := I) (ω := ω) v (.store 2 (tr (d+1)))
  refine ⟨out,?_,(((hw.setPtr _ _).writeTmp _ _).put t (i.eval a) (e.eval a)),?_⟩
  · simpa [C.lower,block,writeTable,off,Nat.add_assoc] using StructuredRAM.Exec.seq eu
      (StructuredRAM.Exec.seq ew (StructuredRAM.Exec.seq (StructuredRAM.Exec.seq en es) (StructuredRAM.Exec.skip out)))
  · exact ((fu.trans (fw.weaken (by omega))).trans (frame_tablePtr _ _ _)).low.trans
      (frame_tmp _ _ _ _ (by omega)).low

theorem lower_out (d : ℕ) (i : N) (e : R) {a : Store} {s : S} (hs : Rep a s) :
    CmdRun I ω (a.writeOut (i.eval a) (e.eval a)) s d ((C.out i e).lower d)
      (i.work+e.work a+(5*i.eval a+5)) := by
  obtain ⟨u,eu,hu,fu,vu⟩ := lower_nat (I := I) (ω := ω) i d hs
  obtain ⟨w,ew,hw,fw,vw⟩ := lower_real (I := I) (ω := ω) e (d+1) hu
  have ep := StructuredRAM.exec_writeAt (I := I) (ω := ω) (tr d) (tr (d+1)) 2 (tr (d+2)) (i.eval a)
    (by unfold tr; omega) (by unfold tr; omega) w ((fw.low d (by omega)).trans vu)
  rw [vw] at ep
  refine ⟨_,?_,(((hw.setPtr 2 (i.eval a : ℤ)).writeTmp (d+2) 0).writeOut (i.eval a) (e.eval a)),?_⟩
  · simpa [C.lower,block,Nat.add_assoc,StructuredRAM.Store.setReg,StructuredRAM.Store.setPtr] using StructuredRAM.Exec.seq eu
      (StructuredRAM.Exec.seq ew (StructuredRAM.Exec.seq ep (StructuredRAM.Exec.skip _)))
  · exact ((fu.trans (fw.weaken (by omega))).trans (frame_tablePtr _ _ _)).low.trans
      (frame_tmp _ _ _ _ (by omega)).low

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
open StructuredRAM (Cmd Prim)
local notation "S" => StructuredRAM.Store
local notation "E" => StructuredRAM.Exec

private def forLoop (idx d : ℕ) (c : Cmd) : Cmd := .whilePos (tr (d+2)) (block [
    copyReg (nr idx) (tr (d+1)),c,ins (.add (tr (d+1)) (tr (d+1)) 7),
    ins (.sub (tr (d+2)) (tr d) (tr (d+1)))])

variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

private theorem for_tail (idx d limit rem start : ℕ) (c : Cmd) (ss : ℕ → Store) (ks : ℕ → ℕ)
    (hb : ∀ j < limit, ∀ s, Rep ((ss j).setN idx j) s → CmdRun I ω (ss (j+1)) s (d+3) c (ks j))
    (hlim : start+rem=limit) (s : S) (hs : Rep (ss start) s)
    (hs0 : s.regs (tr d) = limit) (hs1 : s.regs (tr (d+1)) = start)
    (hs2 : s.regs (tr (d+2)) = rem) :
    ∃ v, E I ω (forLoop idx d c) s v (5*rem+1+∑ j ∈ Finset.Ico start limit, ks j) ∧
      Rep (ss limit) v ∧ Low d s v ∧ v.regs (tr (d+1)) = limit := by
  induction rem generalizing start s with
  | zero =>
    have he : start=limit := by omega
    subst start
    refine ⟨s,?_,hs,Low.refl _ _,hs1⟩
    simpa [forLoop] using (StructuredRAM.Exec.while_false (I := I) (ω := ω) (a := block
      [copyReg (nr idx) (tr (d+1)),c,ins (.add (tr (d+1)) (tr (d+1)) 7),
       ins (.sub (tr (d+2)) (tr d) (tr (d+1)))]) (s := s) (r := tr (d+2)) (by simp [hs2]))
  | succ rem ih =>
    let u := s.setReg (nr idx) (start : ℝ)
    have e0 : E I ω (copyReg (nr idx) (tr (d+1))) s u 1 := by
      simpa [copyReg,ins,Prim.exec,hs1,hs.zeroReg,u] using
        StructuredRAM.Exec.prim (I := I) (ω := ω) s (.sub (nr idx) (tr (d+1)) 3)
    obtain ⟨v,ev,hv,fv⟩ := hb start (by omega) u (hs.setN _ _)
    have hv0 : v.regs (tr d) = limit := (fv d (by omega)).trans ((low_setN (d+3) s idx _ d (by omega)).trans hs0)
    have hv1 : v.regs (tr (d+1)) = start := (fv _ (by omega)).trans ((low_setN (d+3) s idx _ _ (by omega)).trans hs1)
    let w := v.setReg (tr (d+1)) ((start+1 : ℕ) : ℝ)
    have e1 : E I ω (ins (.add (tr (d+1)) (tr (d+1)) 7)) v w 1 := by
      simpa [w,ins,Prim.exec,hv.oneReg,hv1] using
        StructuredRAM.Exec.prim (I := I) (ω := ω) v (.add (tr (d+1)) (tr (d+1)) 7)
    let z := w.setReg (tr (d+2)) (rem : ℝ)
    have hw0 : w.regs (tr d) = limit := ((frame_tmp v (d+1) (d+1) _ le_rfl).low d (by omega)).trans hv0
    have hw1 : w.regs (tr (d+1)) = ((start+1 : ℕ) : ℝ) := by simp [w,StructuredRAM.Store.setReg]
    have hreal : (limit : ℝ) - ((start+1 : ℕ) : ℝ) = rem := by
      have h : (limit : ℝ) = ↑(start+1+rem : ℕ) := by exact_mod_cast (by omega : limit = start+1+rem)
      push_cast at h ⊢; linarith
    have e2 : E I ω (ins (.sub (tr (d+2)) (tr d) (tr (d+1)))) w z 1 := by
      simpa only [z,ins,Prim.exec,hw0,hw1,hreal] using
        StructuredRAM.Exec.prim (I := I) (ω := ω) w (.sub (tr (d+2)) (tr d) (tr (d+1)))
    have f2 : RegisterFrame (d+2) w z := frame_tmp _ _ _ _ le_rfl
    obtain ⟨o,eo,ho,fo,vo⟩ := ih (start+1) (by omega) z ((hv.writeTmp _ _).writeTmp _ _)
      ((f2.low _ (by omega)).trans hw0) ((f2.low _ (by omega)).trans hw1)
      (by simp [z,StructuredRAM.Store.setReg])
    have eb := StructuredRAM.Exec.seq e0 (StructuredRAM.Exec.seq ev
      (StructuredRAM.Exec.seq e1 (StructuredRAM.Exec.seq e2 (StructuredRAM.Exec.skip z))))
    have eg : 0 < s.regs (tr (d+2)) := by rw [hs2]; positivity
    have el := StructuredRAM.Exec.while_true eg eb eo
    refine ⟨o,?_,ho,?_,vo⟩
    · have hc : 5*rem.succ+1+∑ j ∈ Finset.Ico start limit, ks j =
          1+(1+(ks start+(1+(1+0))))+1+(5*rem+1+∑ j ∈ Finset.Ico (start+1) limit, ks j) := by
        rw [Finset.sum_eq_sum_Ico_succ_bot (show start < limit by omega)]; omega
      simpa only [hc,forLoop,block,List.foldr_cons,List.foldr_nil] using el
    · exact ((((low_setN d s idx _).trans (fv.weaken (by omega))).trans
          (frame_tmp v d (d+1) _ (by omega)).low).trans (f2.weaken (by omega)).low).trans fo

theorem lower_for (idx : ℕ) (bound : N) (body : C) (d : ℕ) (ss : ℕ → Store) (ks : ℕ → ℕ)
    (hb : ∀ j < bound.eval (ss 0), ∀ s, Rep ((ss j).setN idx j) s →
      CmdRun I ω (ss (j+1)) s (d+3) (body.lower (d+3)) (ks j))
    {s : S} (hs : Rep (ss 0) s) :
    CmdRun I ω ((ss (bound.eval (ss 0))).setN idx (bound.eval (ss 0))) s d ((C.forN idx bound body).lower d)
      (bound.work+4+5*(bound.eval (ss 0))+∑ j ∈ Finset.range (bound.eval (ss 0)), ks j) := by
  let lim := bound.eval (ss 0)
  obtain ⟨u,eu,hu,fu,vu⟩ := lower_nat (I := I) (ω := ω) bound d hs
  let v := u.setReg (tr (d+1)) 0
  let w := v.setReg (tr (d+2)) (lim : ℝ)
  have e1 : E I ω (ins (.const (tr (d+1)) 0)) u v 1 := StructuredRAM.Exec.prim _ _
  have f1 : RegisterFrame (d+1) u v := frame_tmp _ _ _ _ le_rfl
  have f2 : RegisterFrame (d+2) v w := frame_tmp _ _ _ _ le_rfl
  have hv0 : v.regs (tr d) = lim := (f1.low _ (by omega)).trans vu
  have hv1 : v.regs (tr (d+1)) = 0 := by simp [v,StructuredRAM.Store.setReg]
  have e2 : E I ω (ins (.sub (tr (d+2)) (tr d) (tr (d+1)))) v w 1 := by
    simpa [ins,w,Prim.exec,hv0,hv1] using StructuredRAM.Exec.prim (I := I) (ω := ω) v (.sub (tr (d+2)) (tr d) (tr (d+1)))
  obtain ⟨o,eo,ho,fo,vo⟩ := for_tail idx d lim lim 0 (body.lower (d+3)) ss ks hb (by omega) w
    ((hu.writeTmp _ _).writeTmp _ _) ((f2.low _ (by omega)).trans hv0)
    (by simpa using (f2.low _ (by omega)).trans hv1) (by simp [w,StructuredRAM.Store.setReg])
  let z := o.setReg (nr idx) lim
  have ez : E I ω (copyReg (nr idx) (tr (d+1))) o z 1 := by
    simpa [z,copyReg,ins,Prim.exec,vo,ho.zeroReg] using StructuredRAM.Exec.prim (I := I) (ω := ω) o (.sub (nr idx) (tr (d+1)) 3)
  refine ⟨z,?_,ho.setN idx lim,?_⟩
  · have e := StructuredRAM.Exec.seq eu (StructuredRAM.Exec.seq e1 (StructuredRAM.Exec.seq e2
      (StructuredRAM.Exec.seq eo (StructuredRAM.Exec.seq ez (StructuredRAM.Exec.skip z)))))
    have hr : Finset.Ico 0 lim = Finset.range lim := by ext j; simp
    simp only [hr] at e
    convert e using 1 <;> first | rfl | dsimp [lim]; omega
  · exact ((((fu.trans (f1.weaken (by omega))).trans (f2.weaken (by omega))).low.trans fo).trans (low_setN d o idx _))

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
open StructuredRAM (Cmd Prim)
local notation "S" => StructuredRAM.Store
local notation "E" => StructuredRAM.Exec
variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

theorem lower_value (d dst : ℕ) (i : N) {a : Store} {s : S} (hs : Rep a s) :
    CmdRun I ω (a.setR dst (valueAt I (i.eval a))) s d ((C.value dst i).lower d) (indexWork a i+1) := by
  obtain ⟨u,eu,hu,fu,vu,_⟩ := lower_setIndex (I := I) (ω := ω) d 0 i hs
  let v := valueAt I (i.eval a)
  have ez : E I ω (ins (.value (rr dst) 0)) u (u.setReg (rr dst) v) 1 := by
    have he := StructuredRAM.Exec.prim (I := I) (ω := ω) u (.value (rr dst) 0)
    cases hp : ptrIndex n (i.eval a : ℤ) <;> simpa [ins,Prim.exec,vu,v,valueAt,hp] using he
  exact ⟨_,StructuredRAM.Exec.seq eu ez,hu.setR dst v,fu.trans (low_setR d u dst v)⟩

theorem lower_cost (d dst : ℕ) (i j : N) {a : Store} {s : S} (hs : Rep a s) :
    CmdRun I ω (a.setR dst (pairAt n m (i.eval a) (j.eval a) I.cost)) s d
      ((C.cost dst i j).lower d) (indexWork a i+indexWork a j+1) := by
  obtain ⟨u,eu,hu,fu,vi,_⟩ := lower_setIndex (I := I) (ω := ω) d 0 i hs
  obtain ⟨w,ew,hw,fw,vj,pi⟩ := lower_setIndex (I := I) (ω := ω) d 1 j hu
  have hi : w.ptrs 0 = (i.eval a : ℤ) := (pi 0 (by decide) (by decide)).trans vi
  let val := pairAt n m (i.eval a) (j.eval a) I.cost
  have ez : E I ω (ins (.cost (rr dst) 0 1)) w (w.setReg (rr dst) val) 1 := by
    have he := StructuredRAM.Exec.prim (I := I) (ω := ω) w (.cost (rr dst) 0 1)
    cases hp : ptrIndex n (i.eval a : ℤ) <;> cases hq : ptrIndex m (j.eval a : ℤ) <;>
      simpa [ins,Prim.exec,hi,vj,val,pairAt,hp,hq] using he
  refine ⟨_,?_,hw.setR dst val,(fu.trans fw).trans (low_setR d w dst val)⟩
  simpa [C.lower,block,Nat.add_assoc] using StructuredRAM.Exec.seq eu
    (StructuredRAM.Exec.seq ew (StructuredRAM.Exec.seq ez (StructuredRAM.Exec.skip _)))

theorem lower_cdf (d dst : ℕ) (i j : N) (e : R) {a : Store} {s : S} (hs : Rep a s) :
    CmdRun I ω (a.setR dst (pairAt n m (i.eval a) (j.eval a)
      (fun x y => PandoraKnapsack.Skipping.cdf I x y (e.eval a)))) s d
      ((C.cdf dst i j e).lower d) (indexWork a i+indexWork a j+e.work a+1) := by
  obtain ⟨u,eu,hu,fu,vi,_⟩ := lower_setIndex (I := I) (ω := ω) d 0 i hs
  obtain ⟨v,ev,hv,fv,vj,pi⟩ := lower_setIndex (I := I) (ω := ω) d 1 j hu
  obtain ⟨w,ew,hw,fw,vr⟩ := lower_real (I := I) (ω := ω) e d hv
  have hi : w.ptrs 0 = (i.eval a : ℤ) := (fw.ptrs 0 (by decide)).trans ((pi 0 (by decide) (by decide)).trans vi)
  have hj : w.ptrs 1 = (j.eval a : ℤ) := (fw.ptrs 1 (by decide)).trans vj
  let val := pairAt n m (i.eval a) (j.eval a) (fun x y => PandoraKnapsack.Skipping.cdf I x y (e.eval a))
  have ez : E I ω (ins (.cdf (rr dst) 0 1 (tr d))) w (w.setReg (rr dst) val) 1 := by
    have he := StructuredRAM.Exec.prim (I := I) (ω := ω) w (.cdf (rr dst) 0 1 (tr d))
    cases hp : ptrIndex n (i.eval a : ℤ) <;> cases hq : ptrIndex m (j.eval a : ℤ) <;>
      simpa [ins,Prim.exec,hi,hj,vr,val,pairAt,hp,hq] using he
  refine ⟨_,?_,hw.setR dst val,((fu.trans fv).trans fw.low).trans (low_setR d w dst val)⟩
  simpa [C.lower,block,Nat.add_assoc] using StructuredRAM.Exec.seq eu
    (StructuredRAM.Exec.seq ev (StructuredRAM.Exec.seq ew (StructuredRAM.Exec.seq ez (StructuredRAM.Exec.skip _))))

theorem lower_truncMean (d dst : ℕ) (i j : N) (e : R) {a : Store} {s : S} (hs : Rep a s) :
    CmdRun I ω (a.setR dst (pairAt n m (i.eval a) (j.eval a)
      (fun x y => PandoraKnapsack.Skipping.truncMean I x y (e.eval a)))) s d
      ((C.truncMean dst i j e).lower d) (indexWork a i+indexWork a j+e.work a+1) := by
  obtain ⟨u,eu,hu,fu,vi,_⟩ := lower_setIndex (I := I) (ω := ω) d 0 i hs
  obtain ⟨v,ev,hv,fv,vj,pi⟩ := lower_setIndex (I := I) (ω := ω) d 1 j hu
  obtain ⟨w,ew,hw,fw,vr⟩ := lower_real (I := I) (ω := ω) e d hv
  have hi : w.ptrs 0 = (i.eval a : ℤ) := (fw.ptrs 0 (by decide)).trans ((pi 0 (by decide) (by decide)).trans vi)
  have hj : w.ptrs 1 = (j.eval a : ℤ) := (fw.ptrs 1 (by decide)).trans vj
  let val := pairAt n m (i.eval a) (j.eval a) (fun x y => PandoraKnapsack.Skipping.truncMean I x y (e.eval a))
  have ez : E I ω (ins (.truncMean (rr dst) 0 1 (tr d))) w (w.setReg (rr dst) val) 1 := by
    have he := StructuredRAM.Exec.prim (I := I) (ω := ω) w (.truncMean (rr dst) 0 1 (tr d))
    cases hp : ptrIndex n (i.eval a : ℤ) <;> cases hq : ptrIndex m (j.eval a : ℤ) <;>
      simpa [ins,Prim.exec,hi,hj,vr,val,pairAt,hp,hq] using he
  refine ⟨_,?_,hw.setR dst val,((fu.trans fv).trans fw.low).trans (low_setR d w dst val)⟩
  simpa [C.lower,block,Nat.add_assoc] using StructuredRAM.Exec.seq eu
    (StructuredRAM.Exec.seq ev (StructuredRAM.Exec.seq ew (StructuredRAM.Exec.seq ez (StructuredRAM.Exec.skip _))))

end PandoraKnapsack.Skipping.ArrayRAM

namespace PandoraKnapsack.Skipping.ArrayRAM
open StructuredRAM (Cmd Prim)
local notation "S" => StructuredRAM.Store
local notation "E" => StructuredRAM.Exec
variable {n m T : ℕ} {I : Instance n m T} {ω : ℕ → ℝ}

theorem Exec.lower {a b : Store} {c : C} {k : ℕ} (e : Exec I ω c a b k) (d : ℕ)
    {s : S} (hs : Rep a s) : CmdRun I ω b s d (c.lower d) k := by
  induction e generalizing d s with
  | skip => exact ⟨s,StructuredRAM.Exec.skip _,hs,Low.refl _ _⟩
  | seq ea eb ia ib =>
    obtain ⟨u,eu,hu,fu⟩ := ia d hs
    obtain ⟨v,ev,hv,fv⟩ := ib d hu
    exact ⟨_,StructuredRAM.Exec.seq eu ev,hv,fu.trans fv⟩
  | letN a r z =>
    obtain ⟨u,eu,hu,fu,vu⟩ := lower_nat (I := I) (ω := ω) z d hs
    have ep : E I ω (copyReg (nr r) (tr d)) u (u.setReg (nr r) (z.eval a : ℝ)) 1 := by
      simpa [Prim.exec,copyReg,ins,hu.zeroReg,vu] using
        StructuredRAM.Exec.prim (I := I) (ω := ω) u (.sub (nr r) (tr d) 3)
    exact ⟨_,StructuredRAM.Exec.seq eu ep,hu.setN r _,fu.low.trans (low_setN _ _ _ _)⟩
  | letR a r z =>
    obtain ⟨u,eu,hu,fu,vu⟩ := lower_real (I := I) (ω := ω) z d hs
    have ep : E I ω (copyReg (rr r) (tr d)) u (u.setReg (rr r) (z.eval a)) 1 := by
      simpa [Prim.exec,copyReg,ins,hu.zeroReg,vu] using
        StructuredRAM.Exec.prim (I := I) (ω := ω) u (.sub (rr r) (tr d) 3)
    exact ⟨_,StructuredRAM.Exec.seq eu ep,hu.setR r _,fu.low.trans (low_setR _ _ _ _)⟩
  | put => exact lower_put _ _ _ _ hs
  | out => exact lower_out _ _ _ hs
  | @ite_true a b z yes no k hp ex ih =>
    obtain ⟨u,eu,hu,fu,vu⟩ := lower_real (I := I) (ω := ω) z d hs
    obtain ⟨v,ev,hv,fv⟩ := ih d hu
    refine ⟨v,?_,hv,fu.low.trans fv⟩
    simpa [C.lower,Nat.add_assoc] using StructuredRAM.Exec.seq eu
      (StructuredRAM.Exec.ite_true (r := tr d) (b := no.lower d) (vu ▸ hp) ev)
  | @ite_false a b z yes no k hp ex ih =>
    obtain ⟨u,eu,hu,fu,vu⟩ := lower_real (I := I) (ω := ω) z d hs
    obtain ⟨v,ev,hv,fv⟩ := ih d hu
    refine ⟨v,?_,hv,fu.low.trans fv⟩
    simpa [C.lower,Nat.add_assoc] using StructuredRAM.Exec.seq eu
      (StructuredRAM.Exec.ite_false (r := tr d) (a := yes.lower d) (vu ▸ hp) ev)
  | @while_false a z body hp =>
    obtain ⟨u,eu,hu,fu,vu⟩ := lower_real (I := I) (ω := ω) z d hs
    exact ⟨u,StructuredRAM.Exec.seq eu (StructuredRAM.Exec.while_false (r := tr d) (vu ▸ hp)),hu,fu.low⟩
  | @while_true a a' b z body k l hp eb el ib il =>
    obtain ⟨u,eu,hu,fu,vu⟩ := lower_real (I := I) (ω := ω) z d hs
    obtain ⟨v,ev,hv,fv⟩ := ib d hu
    obtain ⟨w,ew,hw,fw⟩ := il d hv
    change E I ω (.seq (z.lower d) (.whilePos (tr d) (.seq (body.lower d) (z.lower d)))) v w l at ew
    cases ew with
    | @seq _ _ _ _ _ ka kb eg er =>
      refine ⟨w,?_,hw,(fu.low.trans fv).trans fw⟩
      have e := StructuredRAM.Exec.seq eu (StructuredRAM.Exec.while_true (r := tr d)
        (by rw [vu]; exact hp) (StructuredRAM.Exec.seq ev eg) er)
      convert e using 1 <;> first | rfl | omega
  | forN idx bound body ss ks hb ih =>
    apply lower_for idx bound body d ss ks _ hs
    intro j hj u hu
    exact ih j hj (d+3) hu
  | value => exact lower_value _ _ _ hs
  | cost => exact lower_cost _ _ _ _ hs
  | cdf => exact lower_cdf _ _ _ _ _ hs
  | truncMean => exact lower_truncMean _ _ _ _ _ hs
  | uniform a dst =>
    have h := hs.setR dst (ω a.draws)
    let u := {(s.setReg (rr dst) (ω a.draws)) with draws := s.draws+1}
    have e0 : E I ω (ins (.uniform (rr dst))) s u 1 := by
      simpa [ins,u,Prim.exec,hs.draws] using StructuredRAM.Exec.prim (I := I) (ω := ω) s (.uniform (rr dst))
    exact ⟨u,e0,⟨h.natReg,h.realReg,h.zeroReg,h.oneReg,h.table,h.output,by simp [u,hs.draws]⟩,
      low_setR _ _ _ _⟩

private theorem prim_list (ops : List Prim) (s : S) :
    E I ω (block (ops.map ins)) s (ops.foldl (Prim.exec I ω) s) ops.length := by
  induction ops generalizing s with
  | nil => exact StructuredRAM.Exec.skip s
  | cons op ops ih =>
    simpa [block,ins,Nat.add_comm] using StructuredRAM.Exec.seq
      (StructuredRAM.Exec.prim s op) (ih (op.exec I ω s))

private theorem start_rep (I : Instance n m T) (ω : ℕ → ℝ) :
    ∃ s, E I ω prologue (StructuredRAM.initial n m T) s 7 ∧ Rep (initial n m T) s := by
  let ops : List Prim := [.const 7 1,.pset 0 0,.load (nr 0) 0,.pinc 0,.load (nr 1) 0,.pinc 0,.load (rr 0) 0]
  refine ⟨_,prim_list (I := I) (ω := ω) ops (StructuredRAM.initial n m T),?_⟩
  constructor
  · intro j
    by_cases h0 : j = 0 <;> by_cases h1 : j = 1 <;>
      simp [ops,Prim.exec,StructuredRAM.Store.setReg,StructuredRAM.Store.setPtr,StructuredRAM.initial,
        initial,initState,nr,rr,Function.update_apply,h0,h1]
    all_goals first | rfl | omega
  · intro j
    by_cases h0 : j = 0 <;>
      simp [ops,Prim.exec,StructuredRAM.Store.setReg,StructuredRAM.Store.setPtr,StructuredRAM.initial,
        initial,initState,nr,rr,Function.update_apply,h0]
    all_goals try split_ifs
    all_goals first | rfl | omega
  · norm_num [ops,Prim.exec,StructuredRAM.Store.setReg,StructuredRAM.Store.setPtr,StructuredRAM.initial,
        initState,nr,rr,Function.update_apply]
  · norm_num [ops,Prim.exec,StructuredRAM.Store.setReg,StructuredRAM.Store.setPtr,StructuredRAM.initial,
        initState,nr,rr,Function.update_apply]
  · intro t j
    have hpos : 0 < tableOffset t j := by unfold tableOffset; omega
    change (initState n m T).core.mem (-(tableOffset t j : ℤ)) = 0
    have h0 : -(tableOffset t j : ℤ) ≠ 0 := by omega
    have h1 : -(tableOffset t j : ℤ) ≠ 1 := by omega
    have h2 : -(tableOffset t j : ℤ) ≠ 2 := by omega
    simp [initState,h0,h1,h2]
  · intro j; rfl
  · rfl

/-- An execution of the source program gives a halted execution of its fixed instruction list.
Any remaining budget is absorbed by the final accept instruction. -/
theorem Exec.compiled {c : C} {a : Store} {k B : ℕ} (e : Exec I ω c (initial n m T) a k)
    (hB : 7+k ≤ B) :
    Halted (compile c) (run I ω (compile c) B) ∧
    (∀ j : ℕ, (run I ω (compile c) B).core.mem j = a.out j) ∧
    (run I ω (compile c) B).draws = a.draws := by
  obtain ⟨u,ep,hu⟩ := start_rep I ω
  obtain ⟨v,ev,hv,_⟩ := e.lower 0 hu
  have h := StructuredRAM.Exec.seq ep ev
  refine ⟨h.halted hB,?_,?_⟩
  · intro j; change (run I ω (StructuredRAM.program _) B).core.mem j = _
    rw [h.run_eq hB]; exact hv.output j
  · change (run I ω (StructuredRAM.program _) B).draws = _
    rw [h.run_eq hB]; exact hv.draws

/-- Decoding reads only nonnegative output cells. -/
theorem decode_agrees {f g : ℤ → ℝ} (n m : ℕ) (h : ∀ j : ℕ, f j = g j) :
    decodeOutput n m f = decodeOutput n m g := by
  have he (r : ℕ) : decodeEntry n m f r = decodeEntry n m g r := by
    have h1 := h (1+3*r)
    have h2 := h (2+3*r)
    have h3 := h (3+3*r)
    push_cast at h1 h2 h3
    simp only [decodeEntry,h1,h2,h3]
  have h0 : f 0 = g 0 := by simpa using h 0
  simp only [decodeOutput,h0,funext he]

theorem Exec.decode_eq {c : C} {a : Store} {k B : ℕ} (e : Exec I ω c (initial n m T) a k)
    (hB : 7+k ≤ B) :
    decodeOutput n m (run I ω (compile c) B).core.mem =
      decodeOutput n m (fun z => a.out z.toNat) := by
  apply decode_agrees
  intro j
  simpa using (e.compiled hB).2.1 j

end PandoraKnapsack.Skipping.ArrayRAM

open PandoraKnapsack.Skipping PandoraKnapsack.Skipping.ArrayRAM

theorem solution {n m T : ℕ} (I : Instance n m T) (ω : ℕ → ℝ)
    (c : C) (a : Store) (k B : ℕ) (e : Exec I ω c (initial n m T) a k) (hB : 7+k ≤ B) :
    Halted (compile c) (run I ω (compile c) B) ∧
      decodeOutput n m (run I ω (compile c) B).core.mem =
        decodeOutput n m (fun z => a.out z.toNat) :=
  ⟨(e.compiled hB).1,e.decode_eq hB⟩
