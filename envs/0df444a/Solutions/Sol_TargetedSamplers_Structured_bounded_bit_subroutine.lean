-- Prove2me | solution 1 for TargetedSamplers.Structured.bounded_bit_subroutine
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:31:18.848514+00:00
-- url     : https://prove2.me/submissions/a0aa6d5a-a6df-4f97-8cf6-56abfb0befa7

import Definitions.Def_LogCostRAM_StructuredExecution
import Definitions.Def_DirectedHamiltonicity_CycleSearch

namespace TargetedSamplers.Structured

theorem Exec.post {τ inv c s t k} (e : Exec τ inv c s t k) (hs : inv s) : inv t := by
  induction e <;> solve_by_elim

theorem Store.write_fits {s : Store} {width v : ℕ} (h : s.Fits width) (d : ℕ) (hv : v.size ≤ width) :
    (s.write d v).Fits width := by
  intro a
  by_cases he : a = d
  · simpa [Store.write, he] using hv
  · simpa [Store.write, he] using h a

@[simp] theorem Store.write_overwrite (s : Store) (a x y : ℕ) : (s.write a x).write a y = s.write a y := by
  simp [Store.write]

def Op.written (τ : Tapes) (s : Store) : Op → ℕ
  | .const _ c => c
  | .add _ a b => s.mem a + s.mem b
  | .sub _ a b => s.mem a - s.mem b
  | .load _ a => s.mem (s.mem a)
  | .store _ b => s.mem b
  | .input _ a => bitVal τ.input[s.mem a]?
  | .coin _ a => bitVal τ.coins[s.mem a]?
  | .output _ => 0

theorem Op.eval_fits (p : Op) (τ : Tapes) {s : Store} {b : ℕ}
    (hi : s.Fits b) (hw : (p.written τ s).size ≤ b) : (p.eval τ s).Fits b := by
  cases p <;> first | exact Store.write_fits hi _ hw | exact hi

structure Result where
  last : Store
  steps : ℕ
  writeWidth : ℕ

/-- Evaluation charges the actual control transfers and records the largest value written. -/
def Fragment.run (τ : Tapes) (s : Store) : Fragment → Result
  | .skip => ⟨s,0,0⟩
  | .op o => ⟨o.eval τ s,1,(o.written τ s).size⟩
  | .seq x y =>
    let p := x.run τ s
    let q := y.run τ p.last
    ⟨q.last,p.steps+q.steps,max p.writeWidth q.writeWidth⟩
  | .branch a b yes no =>
    if s.mem a ≤ s.mem b then
      let p := yes.run τ s
      ⟨p.last,1+p.steps,p.writeWidth⟩
    else
      let p := no.run τ s
      ⟨p.last,1+p.steps+1,p.writeWidth⟩

theorem Fragment.exec (f : Fragment) (τ : Tapes) (s : Store) (b : ℕ)
    (hs : s.Fits b) (hw : (f.run τ s).writeWidth ≤ b) :
    Exec τ (fun st => st.Fits b) f.cmd s (f.run τ s).last (f.run τ s).steps := by
  induction f generalizing s with
  | skip => exact .skip s
  | op o => exact .op s o (o.eval_fits τ hs hw)
  | seq x y ix iy =>
    obtain ⟨hx,hy⟩ := max_le_iff.mp hw
    have first := ix s hs hx
    exact .seq first (iy _ (first.post hs) hy)
  | branch a b y n iy ino =>
    by_cases h : s.mem a ≤ s.mem b
    · simp only [run,h,if_true] at hw ⊢
      exact .yes h (iy s hs hw)
    · simp only [run,h,if_false] at hw ⊢
      exact .no h (ino s hs hw)


end TargetedSamplers.Structured

namespace TargetedSamplers.Structured

@[simp] theorem Cmd.compile_length (c : Cmd) (pc : ℕ) : (c.compile pc).length = c.len := by
  induction c generalizing pc <;> simp_all [compile, len] <;> omega

/-- A block may be embedded between arbitrary instructions. All internal jump labels are absolute. -/
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

/-- A live, ordinary machine state at the specified instruction, memory and output. -/
structure Located (st : State) (pc : ℕ) (s : Store) : Prop where
  counter : st.pc = pc
  live : st.halted = false
  normal : st.bot = false
  memory : st.mem = s.mem
  output : st.out = s.out

theorem step_op {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]? = some p.instruction) : Located (P.step τ st) (pc+1) (p.eval τ s) := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  cases p <;> constructor <;> simp_all [Op.instruction, Op.eval, Program.step, State.write, Store.write]

theorem step_jle {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (a b dst : ℕ) (hp : P[pc]? = some (.jle a b dst)) :
    Located (P.step τ st) (if s.mem a ≤ s.mem b then dst else pc+1) s := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  constructor <;> simp [Program.step, hc, hh, hb, hm, ho, hp]

theorem step_jump {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (dst : ℕ) (hp : P[pc]? = some (jump dst)) : Located (P.step τ st) dst s := by
  simpa using step_jle τ h 0 0 dst hp

theorem branch_sites {P pc a b y n} (h : Contains P pc ((Cmd.branch a b y n).compile pc)) :
    P[pc]? = some (.jle a b (pc+1+n.len+1)) ∧ Contains P (pc+1) (n.compile (pc+1)) ∧
    P[pc+1+n.len]? = some (jump (pc+1+n.len+1+y.len)) ∧
    Contains P (pc+1+n.len+1) (y.compile (pc+1+n.len+1)) := by
  unfold Cmd.compile at h
  exact ⟨h.left.one, h.right.left, by simpa using h.right.right.left.one, by simpa using h.right.right.right⟩

theorem loop_sites {P pc a b body} (h : Contains P pc ((Cmd.whileGt a b body).compile pc)) :
    P[pc]? = some (.jle a b (pc+1+body.len+1)) ∧ Contains P (pc+1) (body.compile (pc+1)) ∧
    P[pc+1+body.len]? = some (jump pc) := by
  unfold Cmd.compile at h
  exact ⟨h.left.one, h.right.left, by simpa using h.right.right.one⟩


end TargetedSamplers.Structured

namespace TargetedSamplers.Structured

/-- Log-cost of a data instruction with its actual operands. This expression is independent
of the bit widths of registers that the instruction never inspects. -/
def Op.charge (τ : Tapes) (s : Store) : Op → ℕ
  | .const d c => 1+d.size+c.size
  | .add d a b => 1+d.size+a.size+b.size+(s.mem a).size+(s.mem b).size+(s.mem a+s.mem b).size
  | .sub d a b => 1+d.size+a.size+b.size+(s.mem a).size+(s.mem b).size+(s.mem a-s.mem b).size
  | .load d a => 1+d.size+a.size+(s.mem a).size+(s.mem (s.mem a)).size
  | .store a b => 1+a.size+b.size+(s.mem a).size+(s.mem b).size
  | .input d a => 1+d.size+a.size+(s.mem a).size+(bitVal τ.input[s.mem a]?).size
  | .coin d a => 1+d.size+a.size+(s.mem a).size+(bitVal τ.coins[s.mem a]?).size
  | .output a => 1+a.size+(s.mem a).size

def testCharge (s : Store) (a b dst : ℕ) := 1+a.size+b.size+(s.mem a).size+(s.mem b).size+dst.size

/-- Exact bit cost of a loop-free structured block relocated to an absolute program address. -/
def Fragment.charge (τ : Tapes) (s : Store) (pc : ℕ) : Fragment → ℕ
  | .skip => 0
  | .op o => o.charge τ s
  | .seq x y => x.charge τ s pc + y.charge τ (x.run τ s).last (pc+x.cmd.len)
  | .branch a b y n =>
    let yesPC := pc+1+n.cmd.len+1
    testCharge s a b yesPC +
      if s.mem a ≤ s.mem b then y.charge τ s yesPC
      else n.charge τ s (pc+1) + testCharge (n.run τ s).last 0 0 (yesPC+y.cmd.len)

def Travels (P : Program) (τ : Tapes) (s t : State) (steps cost : ℕ) : Prop :=
  (P.step τ)^[steps] s=t ∧ t.work=s.work+cost

theorem Travels.trans {P τ s m t k j a b} (e : Travels P τ s m k a) (f : Travels P τ m t j b) :
    Travels P τ s t (k+j) (a+b) := by
  constructor
  · rw [Nat.add_comm k j,Function.iterate_add_apply,e.1,f.1]
  · rw [f.2,e.2,Nat.add_assoc]

theorem op_travels {P : Program} {τ : Tapes} {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]?=some p.instruction) :
    Travels P τ st (P.step τ st) 1 (p.charge τ s) := by
  refine ⟨rfl,?_⟩
  obtain ⟨hc,live,_,mem,_⟩ := h
  cases p <;> simp_all [Program.step,Op.instruction,Op.charge,Nat.add_assoc]

theorem test_travels {P : Program} {τ : Tapes} {st pc s} (h : Located st pc s)
    (a b dst : ℕ) (hp : P[pc]?=some (.jle a b dst)) :
    Travels P τ st (P.step τ st) 1 (testCharge s a b dst) := by
  refine ⟨rfl,?_⟩
  simp [Program.step,h.counter,h.live,hp,h.memory,testCharge,Nat.add_assoc]

/-- The machine-level accounting matches every executed instruction, including branch jumps,
when unrelated memory cells may hold arbitrarily long words. -/
theorem Fragment.compile_charge (f : Fragment) (P : Program) (τ : Tapes) (pc : ℕ) (st : State)
    (s : Store) (sub : Contains P pc (f.cmd.compile pc)) (loc : Located st pc s) :
    ∃ t, Travels P τ st t (f.run τ s).steps (f.charge τ s pc) ∧
      Located t (pc+f.cmd.len) (f.run τ s).last := by
  induction f generalizing pc st s with
  | skip => exact ⟨st,⟨rfl,by simp [charge]⟩,by simpa [cmd,Cmd.len,run] using loc⟩
  | op o => exact ⟨_,op_travels loc o sub.one,step_op τ loc o sub.one⟩
  | seq x y ix iy =>
    obtain ⟨m,hx,mLoc⟩ := ix pc st s sub.left loc
    obtain ⟨t,hy,stop⟩ := iy (pc+x.cmd.len) m (x.run τ s).last (by simpa using sub.right) mLoc
    exact ⟨t,hx.trans hy,by simpa [cmd,Cmd.len,run,Nat.add_assoc] using stop⟩
  | branch a b yes no iy ino =>
    obtain ⟨ht,hn,hj,hy⟩ := branch_sites sub
    have step := step_jle τ loc a b _ ht
    have cost := test_travels (τ:=τ) loc a b _ ht
    by_cases take : s.mem a ≤ s.mem b
    · rw [if_pos take] at step
      obtain ⟨t,ex,stop⟩ := iy _ _ s hy step
      refine ⟨t,?_,?_⟩
      · simpa only [run,charge,if_pos take] using cost.trans ex
      · simpa [cmd,Cmd.len,run,take,Nat.add_assoc] using stop
    · rw [if_neg take] at step
      obtain ⟨m,ex,ml⟩ := ino _ _ s hn step
      have jump := step_jump τ ml _ hj
      have back := test_travels (τ:=τ) ml 0 0 _ hj
      refine ⟨P.step τ m,?_,?_⟩
      · simpa only [run,charge,if_neg take,Nat.add_assoc] using (cost.trans ex).trans back
      · simpa [cmd,Cmd.len,run,take,Nat.add_assoc] using jump

end TargetedSamplers.Structured

namespace TargetedSamplers.Structured.GuestMemory

/-- Two cells per guest address. The other two residues are available to the caller. -/
def tag (a : ℕ) := 64+4*a
def value (a : ℕ) := tag a+1
def view (s : Store) (epoch a : ℕ) : ℕ := if s.mem (tag a)=epoch then s.mem (value a) else 0
def Valid (s : Store) (epoch : ℕ) := ∀ a, s.mem (tag a) ≤ epoch

theorem next_empty {s : Store} {epoch : ℕ} (h : Valid s epoch) :
    view s (epoch+1) = fun _ => 0 := by
  funext a;have := h a;simp [view,show s.mem (tag a) ≠ epoch+1 by omega]

/-- Registers 8 and 10 hold the guest address and invocation number. Register 9 carries
the transferred word. The heap cells have addresses at least 64. -/
def address : Fragment := Structured.sequence [
  .op (.add 11 8 8), .op (.add 11 11 11), .op (.const 12 64), .op (.add 11 11 12)]

def nextCell : Fragment := Structured.sequence [.op (.const 12 1), .op (.add 11 11 12)]
def fetch : Fragment := .seq address <| Structured.sequence [.op (.load 13 11),
  .branch 10 13 (.seq nextCell (.op (.load 9 11))) (.op (.const 9 0))]
def save : Fragment := .seq address <| Structured.sequence [
  .op (.store 11 10), nextCell, .op (.store 11 9)]

private theorem eqTag (a : ℕ) : a+a+(a+a)+64=tag a := by unfold tag;ring

theorem fetch_result (τ : Tapes) (s : Store) (e a : ℕ) (addr : s.mem 8=a) (clock : s.mem 10=e)
    (valid : Valid s e) :
    let t := (fetch.run τ s).last
    t.mem 9=view s e a ∧ t.out=s.out ∧
      ∀ i, i≠9 → i≠11 → i≠12 → i≠13 → t.mem i=s.mem i := by
  have far : 64≤tag a := by simp [tag]
  have lo := valid a
  by_cases hit : s.mem (tag a)=e
  · simp (disch := omega) [fetch,address,nextCell,Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,addr,clock,eqTag,view,value,hit]
    intro i i9 i11 i12 i13;simp [i9,i11,i12,i13]
  · have lt : ¬e ≤ s.mem (tag a) := by omega
    simp (disch := omega) [fetch,address,nextCell,Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,addr,clock,eqTag,view,value,hit,lt]
    intro i i9 i11 i12 i13;simp [i9,i11,i12,i13]

theorem save_result (τ : Tapes) (s : Store) (e a w : ℕ) (addr : s.mem 8=a) (clock : s.mem 10=e)
    (data : s.mem 9=w) (valid : Valid s e) :
    let t := (save.run τ s).last
    Valid t e ∧ view t e = Function.update (view s e) a w ∧ t.out=s.out ∧
      ∀ i, i≠11 → i≠12 → i≠tag a → i≠value a → t.mem i=s.mem i := by
  let t := (save.run τ s).last
  have far : 64≤tag a := by simp [tag]
  have frm (i : ℕ) (x : i≠11) (y : i≠12) (z : i≠tag a) (v : i≠value a) : t.mem i=s.mem i := by
    simp (disch := omega) [t,save,address,nextCell,Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,addr,clock,data,eqTag,value] at v ⊢
  have stamp : t.mem (tag a)=e := by
    simp (disch := omega) [t,save,address,nextCell,Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,addr,clock,data,eqTag]
  have word : t.mem (value a)=w := by
    simp (disch := omega) [t,save,address,nextCell,Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,addr,clock,data,eqTag,value]
  have tg {i} (h : i≠a) : t.mem (tag i)=s.mem (tag i) := by
    apply frm <;> simp only [value,tag] <;> omega
  have vl {i} (h : i≠a) : t.mem (value i)=s.mem (value i) := by
    apply frm <;> simp only [value,tag] <;> omega
  refine ⟨?_,?_,rfl,frm⟩
  · intro i
    by_cases h : i=a
    · exact h ▸ stamp.le
    · change t.mem (tag i) ≤ e;rw [tg h];exact valid i
  · funext i
    by_cases h : i=a
    · subst i;change view t e a=_;simp [view,stamp,word]
    · change view t e i=_;simp [view,tg h,vl h,h]

private theorem address_width (a : ℕ) : (value a).size ≤ a.size+7 := by
  apply Nat.size_le.mpr
  rw [pow_add]
  have top := Nat.lt_size_self a
  have positive := Nat.two_pow_pos a.size
  dsimp [value,tag]
  norm_num
  omega

private theorem size_num (a : ℕ) (small : a ≤ 65) : a.size ≤ 7 :=
  (Nat.size_le_size small).trans (by decide)

/-- Reading and updating the guest memory charge the bit lengths of the requested address,
transferred value, invocation number and relocated branch target. -/
theorem save_charge (τ : Tapes) (s : Store) (pc a e w : ℕ)
    (addr : s.mem 8=a) (clock : s.mem 10=e) (data : s.mem 9=w) :
    save.charge τ s pc ≤ 512*(1+a.size+e.size+w.size) := by
  have far : 64≤tag a := by simp [tag]
  have sizes (i : ℕ) (hi : i ≤ value a) : i.size ≤ a.size+7 :=
    (Nat.size_le_size hi).trans (address_width a)
  have b1 := sizes (a+a) (by unfold value tag;omega)
  have b2 := sizes (a+a+(a+a)) (by unfold value tag;omega)
  have b3 := sizes (tag a) (by simp [value])
  have b4 := address_width a
  simp (disch := omega) [save,address,nextCell,Structured.sequence,Fragment.charge,Fragment.run,Op.charge,
    Op.eval,Store.write,Function.update_apply,addr,clock,data,eqTag] 
  change _ ≤ _
  have c8 := size_num 8 (by decide)
  have c9 := size_num 9 (by decide)
  have c10 := size_num 10 (by decide)
  have c11 := size_num 11 (by decide)
  have c12 := size_num 12 (by decide)
  have c64 := size_num 64 (by decide)
  unfold value at b4
  omega


theorem fetch_charge (τ : Tapes) (s : Store) (pc a e : ℕ) (addr : s.mem 8=a) (clock : s.mem 10=e)
    (zero : s.mem 0=0) (valid : Valid s e) :
    fetch.charge τ s pc ≤ 512*(1+(pc+64).size+a.size+e.size+(view s e a).size) := by
  have far : 64≤tag a := by simp [tag]
  have sizes (i : ℕ) (hi : i ≤ value a) : i.size ≤ a.size+7 :=
    (Nat.size_le_size hi).trans (address_width a)
  have b1 := sizes (a+a) (by unfold value tag;omega)
  have b2 := sizes (a+a+(a+a)) (by unfold value tag;omega)
  have b3 := sizes (tag a) (by simp [value])
  have b4 := address_width a
  have stamp := valid a
  have bt := Nat.size_le_size stamp
  have c0 : (0:ℕ).size=0 := rfl
  have c1 : (1:ℕ).size=1 := rfl
  have c8 := size_num 8 (by decide)
  have c9 := size_num 9 (by decide)
  have c10 := size_num 10 (by decide)
  have c11 := size_num 11 (by decide)
  have c12 := size_num 12 (by decide)
  have c13 := size_num 13 (by decide)
  have c64 := size_num 64 (by decide)
  have code (j : ℕ) (h : j ≤ pc+64) := Nat.size_le_size h
  have branchPC := code (pc+4+1+1+1+1) (by omega)
  have pastPC := code (pc+4+1+1+1+1+3) (by omega)
  unfold value at b4
  by_cases hit : s.mem (tag a)=e
  · simp (disch := omega) [fetch,address,nextCell,Structured.sequence,Fragment.charge,Fragment.run,
      Fragment.cmd,Cmd.len,Op.charge,Op.eval,Store.write,Function.update_apply,addr,clock,zero,eqTag,view,value,hit,testCharge]
    omega
  · have lt : ¬e ≤ s.mem (tag a) := by omega
    simp (disch := omega) [fetch,address,nextCell,Structured.sequence,Fragment.charge,Fragment.run,
      Fragment.cmd,Cmd.len,Op.charge,Op.eval,Store.write,Function.update_apply,addr,clock,zero,eqTag,view,value,hit,lt,testCharge]
    omega

end TargetedSamplers.Structured.GuestMemory

namespace TargetedSamplers.Structured.GuestMemory

/-- General-purpose host temporaries are separate from the epoch-memory transfer registers. -/
abbrev Reg := Fin 32
def loc (r : Reg) := 20+r.val
def inputCell (i : ℕ) := tag i+2
def callerCell (i : ℕ) := tag i+3

structure ViewState where
  regs : Reg → ℕ
  heap : ℕ → ℕ

def ViewState.set (v : ViewState) (r : Reg) (z : ℕ) : ViewState := {v with regs := Function.update v.regs r z}
def ViewState.put (v : ViewState) (a z : ℕ) : ViewState := {v with heap := Function.update v.heap a z}
def snap (s : Store) (e : ℕ) : ViewState := ⟨fun r => s.mem (loc r),view s e⟩

structure Base (s : Store) (e : ℕ) : Prop where
  zero : s.mem 0 = 0
  clock : s.mem 10 = e
  valid : Valid s e

structure Frame (s t : Store) : Prop where
  output : t.out=s.out
  input : ∀ i, t.mem (inputCell i)=s.mem (inputCell i)
  caller : ∀ i, t.mem (callerCell i)=s.mem (callerCell i)

attribute [local irreducible] fetch save

theorem Frame.refl (s : Store) : Frame s s := ⟨rfl,fun _ => rfl,fun _ => rfl⟩
theorem Frame.trans {s t u : Store} (p : Frame s t) (q : Frame t u) : Frame s u :=
  ⟨q.output.trans p.output,fun i => (q.input i).trans (p.input i),fun i => (q.caller i).trans (p.caller i)⟩

private theorem fixed_low (s : Store) (d x : ℕ) (low : d<64) (i : ℕ) (hi : 64 ≤ i) :
    (s.write d x).mem i=s.mem i := by simp [Store.write,show i≠d by omega]

theorem Base.low {s : Store} {e : ℕ} (p : Base s e) (d x : ℕ) (h : d<64) (h0 : d≠0) (hc : d≠10) :
    Base (s.write d x) e := by
  refine ⟨by simp [Store.write,Ne.symm h0,p.zero],by simp [Store.write,Ne.symm hc,p.clock],fun i => ?_⟩
  rw [fixed_low s d x h _ (by simp [tag])];exact p.valid i

theorem low_frame (s : Store) (d x : ℕ) (h : d<64) : Frame s (s.write d x) :=
  ⟨rfl,fun i => fixed_low s d x h _ (by unfold inputCell tag;omega),
    fun i => fixed_low s d x h _ (by unfold callerCell tag;omega)⟩

theorem low_heap (s : Store) (e d x : ℕ) (h : d<64) : view (s.write d x) e=view s e := by
  funext i
  simp only [view,fixed_low s d x h _ (show 64 ≤ tag i by simp [tag]),fixed_low s d x h _ (show 64 ≤ value i by unfold value tag;omega)]

theorem low_scratch (s : Store) (e d x : ℕ) (h : d<20) : snap (s.write d x) e=snap s e := by
  unfold snap;rw [low_heap _ _ _ _ (by omega)]
  apply congrArg (fun r => ViewState.mk r _)
  funext i; simp [Store.write,show loc i ≠ d by unfold loc;omega]

theorem low_local (s : Store) (e : ℕ) (d : Reg) (x : ℕ) : snap (s.write (loc d) x) e=(snap s e).set d x := by
  have low : loc d<64 := by unfold loc;have := d.isLt;omega
  unfold snap ViewState.set;rw [low_heap _ _ _ _ low]
  apply congrArg (fun r => ViewState.mk r _)
  funext i
  have eq : loc i = loc d ↔ i=d := by simp [loc,Fin.ext_iff]
  simp [Store.write,Function.update_apply,eq]

inductive Micro where
  | skip
  | lit (dst : Reg) (word : ℕ)
  | add (dst left right : Reg)
  | sub (dst left right : Reg)
  | read (dst key : Reg)
  | write (key src : Reg)
  | input (dst key : Reg)
  | coin (dst key : Reg)
  | seq (x y : Micro)
  | branch (left right : Reg) (yes no : Micro)

def Micro.eval (input : ℕ → ℕ) (coins : List Bool) (v : ViewState) : Micro → ViewState
  | .skip => v
  | .lit d x => v.set d x
  | .add d a b => v.set d (v.regs a+v.regs b)
  | .sub d a b => v.set d (v.regs a-v.regs b)
  | .read d a => v.set d (v.heap (v.regs a))
  | .write a b => v.put (v.regs a) (v.regs b)
  | .input d a => v.set d (input (v.regs a))
  | .coin d a => v.set d (bitVal coins[v.regs a]?)
  | .seq x y => y.eval input coins (x.eval input coins v)
  | .branch a b y n => if v.regs a ≤ v.regs b then y.eval input coins v else n.eval input coins v

def Micro.code : Micro → Fragment
  | .skip => .skip
  | .lit d x => .op (.const (loc d) x)
  | .add d a b => .op (.add (loc d) (loc a) (loc b))
  | .sub d a b => .op (.sub (loc d) (loc a) (loc b))
  | .coin d a => .op (.coin (loc d) (loc a))
  | .read d a => Structured.sequence [.op (.add 8 (loc a) 0),fetch,.op (.add (loc d) 9 0)]
  | .write a b => Structured.sequence [.op (.add 8 (loc a) 0),.op (.add 9 (loc b) 0),save]
  | .input d a => Structured.sequence [.op (.add 8 (loc a) (loc a)),.op (.add 8 8 8),.op (.const 11 66),
      .op (.add 8 8 11),.op (.load (loc d) 8)]
  | .seq x y => .seq x.code y.code
  | .branch a b y n => .branch (loc a) (loc b) y.code n.code

structure Simulates (s t : Store) (e : ℕ) (v : ViewState) : Prop where
  base : Base t e
  state : snap t e = v
  frame : Frame s t

private theorem local_sim (s : Store) (e : ℕ) (h : Base s e) (d : Reg) (x : ℕ) :
    Simulates s (s.write (loc d) x) e ((snap s e).set d x) := by
  have l := d.isLt
  exact ⟨h.low _ _ (by unfold loc;omega) (by unfold loc;omega) (by unfold loc;omega),low_local ..,
    low_frame _ _ _ (by unfold loc;omega)⟩

private theorem scratch_sim (s : Store) (e : ℕ) (h : Base s e) (d x : ℕ) (lo : d<20) (nz : d≠0) (nc : d≠10) :
    Simulates s (s.write d x) e (snap s e) :=
  ⟨h.low d x (by omega) nz nc,low_scratch _ _ _ _ lo,low_frame _ _ _ (by omega)⟩

private theorem fetch_sim (s : Store) (e : ℕ) (h : Base s e) (a : ℕ) (atA : s.mem 8=a) (τ : Tapes) :
    let t := (fetch.run τ s).last
    Simulates s t e (snap s e) ∧ t.mem 9=(snap s e).heap a := by
  let t := (fetch.run τ s).last
  obtain ⟨bit,out,rest⟩ := fetch_result τ s e a atA h.clock h.valid
  have high (i : ℕ) (hi : 20 ≤ i) : t.mem i=s.mem i := rest i (by omega) (by omega) (by omega) (by omega)
  have heap (i : ℕ) : view t e i=view s e i := by
    simp only [view,high (tag i) (by unfold tag;omega),high (value i) (by unfold value tag;omega)]
  refine ⟨⟨⟨(rest 0 (by decide) (by decide) (by decide) (by decide)).trans h.zero,
    (rest 10 (by decide) (by decide) (by decide) (by decide)).trans h.clock,
    fun i => (high (tag i) (by unfold tag;omega)).symm ▸ h.valid i⟩,?_,
    ⟨out,fun i => high (inputCell i) (by unfold inputCell tag;omega),fun i => high (callerCell i) (by unfold callerCell tag;omega)⟩⟩,bit⟩
  change ViewState.mk (fun i => t.mem (loc i)) (view t e)=_
  rw [funext heap,show (fun i => t.mem (loc i))=(fun i => s.mem (loc i)) from funext (fun i => high _ (by unfold loc;omega))]
  rfl

private theorem write_sim (s : Store) (e : ℕ) (h : Base s e) (a w : ℕ) (atA : s.mem 8=a)
    (val : s.mem 9=w) (τ : Tapes) : Simulates s (save.run τ s).last e ((snap s e).put a w) := by
  let t := (save.run τ s).last
  obtain ⟨valid,heap,out,rest⟩ := save_result τ s e a w atA h.clock val h.valid
  have low (i : ℕ) (hi : i<64) (h1 : i≠11) (h2 : i≠12) : t.mem i=s.mem i :=
    rest i h1 h2 (by unfold tag;omega) (by unfold value tag;omega)
  have locals (i : Reg) : t.mem (loc i)=s.mem (loc i) := by
    have := i.isLt;apply low <;> unfold loc <;> omega
  refine ⟨⟨(low 0 (by decide) (by decide) (by decide)).trans h.zero,
    (low 10 (by decide) (by decide) (by decide)).trans h.clock,valid⟩,?_,⟨out,?_,?_⟩⟩
  · change ViewState.mk _ (view t e)=ViewState.mk _ _
    rw [heap,funext locals]; rfl
  · intro i;apply rest <;> simp only [inputCell,value,tag] <;> omega
  · intro i;apply rest <;> simp only [callerCell,value,tag] <;> omega


private theorem read_code (τ : Tapes) (s : Store) (e : ℕ) (h : Base s e) (d a : Reg) :
    Simulates s (((Micro.read d a).code.run τ s).last) e ((snap s e).set d ((snap s e).heap ((snap s e).regs a))) := by
  let k := s.mem (loc a)
  let u := s.write 8 k
  let t := (fetch.run τ u).last
  have first := scratch_sim s e h 8 k (by decide) (by decide) (by decide)
  obtain ⟨got,bit⟩ := fetch_sim u e first.base k (by simp [u,Store.write]) τ
  have fin := local_sim t e got.base d (t.mem 9)
  have raw : ((Micro.read d a).code.run τ s).last = t.write (loc d) (t.mem 9) := by
    simp only [Micro.code,Structured.sequence,Fragment.run,Op.eval,h.zero,Nat.add_zero]
    change t.write _ (t.mem 9+t.mem 0)=_; rw [got.base.zero,Nat.add_zero]
  rw [raw]
  refine ⟨fin.base,?_,(first.frame.trans got.frame).trans fin.frame⟩
  rw [fin.state,got.state,bit,first.state]
  rfl

private theorem write_code (τ : Tapes) (s : Store) (e : ℕ) (h : Base s e) (a b : Reg) :
    Simulates s (((Micro.write a b).code.run τ s).last) e ((snap s e).put ((snap s e).regs a) ((snap s e).regs b)) := by
  let k := s.mem (loc a)
  let w := s.mem (loc b)
  let u := s.write 8 k
  let t := u.write 9 w
  have one := scratch_sim s e h 8 k (by decide) (by decide) (by decide)
  have two := scratch_sim u e one.base 9 w (by decide) (by decide) (by decide)
  have fin := write_sim t e two.base k w (by simp [t,u,Store.write]) (by simp [t,Store.write]) τ
  have raw : ((Micro.write a b).code.run τ s).last = (save.run τ t).last := by
    simp only [Micro.code,Structured.sequence,Fragment.run,Op.eval,h.zero,Nat.add_zero]
    change (save.run τ (u.write 9 (u.mem (loc b)+u.mem 0))).last = _
    rw [one.base.zero,Nat.add_zero]
    have off : loc b ≠ 8 := by unfold loc;omega
    simp [u,t,w,Store.write,off]
  rw [raw]
  refine ⟨fin.base,?_,(one.frame.trans two.frame).trans fin.frame⟩
  rw [fin.state,two.state,one.state]
  rfl

private theorem input_code (τ : Tapes) (s : Store) (e : ℕ) (h : Base s e) (d a : Reg) :
    Simulates s (((Micro.input d a).code.run τ s).last) e ((snap s e).set d (s.mem (inputCell ((snap s e).regs a)))) := by
  let k := s.mem (loc a)
  let v := k+k
  let u := s.write 8 v
  let t := u.write 8 (v+v)
  let m := t.write 11 66
  let z := m.write 8 (inputCell k)
  have one := scratch_sim s e h 8 v (by decide) (by decide) (by decide)
  have two := scratch_sim u e one.base 8 (v+v) (by decide) (by decide) (by decide)
  have three := scratch_sim t e two.base 11 66 (by decide) (by decide) (by decide)
  have four := scratch_sim m e three.base 8 (inputCell k) (by decide) (by decide) (by decide)
  let frame := ((one.frame.trans two.frame).trans three.frame).trans four.frame
  have fin := local_sim z e four.base d (z.mem (inputCell k))
  have raw : ((Micro.input d a).code.run τ s).last=z.write (loc d) (z.mem (inputCell k)) := by
    have val : s.mem (loc a)+s.mem (loc a)+(s.mem (loc a)+s.mem (loc a))+66=inputCell k := by
      unfold k inputCell tag;ring
    simp (disch := omega) [Micro.code,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      z,m,t,u,v,k,val,show 64 ≤ inputCell k by unfold inputCell tag;omega]
  rw [raw]
  refine ⟨fin.base,?_,frame.trans fin.frame⟩
  rw [fin.state,four.state,three.state,two.state,one.state,frame.input k]
  rfl

/-- A finite macro sequence manipulates local words and the lazy-cleared guest heap.
Each instruction is realized by native arithmetic, loads, stores and tape reads. -/
theorem Micro.correct (m : Micro) (τ : Tapes) (s : Store) (e : ℕ) (h : Base s e) :
    Simulates s (m.code.run τ s).last e (m.eval (fun i => s.mem (inputCell i)) τ.coins (snap s e)) := by
  induction m generalizing s with
  | skip => exact ⟨h,rfl,Frame.refl _⟩
  | lit d x => exact local_sim s e h d x
  | add d a b => exact local_sim s e h d _
  | sub d a b => exact local_sim s e h d _
  | coin d a => exact local_sim s e h d _
  | read d a => exact read_code τ s e h d a
  | write a b => exact write_code τ s e h a b
  | input d a => exact input_code τ s e h d a
  | seq x y ix iy =>
    let u := (x.code.run τ s).last
    have first := ix s h
    have last := iy u first.base
    refine ⟨last.base,?_,first.frame.trans last.frame⟩
    change snap ((y.code.run τ u).last) e = _
    rw [last.state,first.state,funext first.frame.input]; rfl
  | branch a b y n iy ino =>
    by_cases isLE : s.mem (loc a) ≤ s.mem (loc b)
    · have cond : (snap s e).regs a ≤ (snap s e).regs b := isLE
      simpa only [code,Fragment.run,eval,if_pos isLE,if_pos cond] using iy s h
    · have cond : ¬ (snap s e).regs a ≤ (snap s e).regs b := isLE
      simpa only [code,Fragment.run,eval,if_neg isLE,if_neg cond] using ino s h

end TargetedSamplers.Structured.GuestMemory

namespace DirectedHamiltonicity.Main.CycleReduction.CoinWindow

open TargetedSamplers TargetedSamplers.Structured FiniteSampling

/-- A bounded virtual coin tape. Missing bits of the host tape count as zero inside the window. -/
def window (coins : List Bool) (start length : ℕ) : List Bool :=
  List.ofFn fun i : Fin length => coins[start+i.val]?.getD false

theorem read_window (coins : List Bool) (start len i : ℕ) :
    bitVal (window coins start len)[i]? =
      if i<len then (coins[start+i]?.getD false).toNat else 2 := by
  by_cases h : i<len <;> simp [window,h,bitVal]

theorem parity_window (n length : ℕ) (coins : List Bool) (j : Fin (2*majorityHalf n)) :
    List.ofFn ((panelFromTape n length coins).2 j) =
      window coins (trials n*seedWidth n + length*j.val) length := by
  apply congrArg List.ofFn
  funext i
  change coins[(trials n*seedWidth n+(i.val+length*j.val))]?.getD false = _
  change _ = coins[(trials n*seedWidth n+length*j.val)+i.val]?.getD false
  rw [show trials n*seedWidth n+(i.val+length*j.val)=trials n*seedWidth n+length*j.val+i.val by omega]

end DirectedHamiltonicity.Main.CycleReduction.CoinWindow

namespace DirectedHamiltonicity.Main.CycleReduction.Guest

open TargetedSamplers TargetedSamplers.Structured GuestMemory

/-- The first registers of the microprogram hold the guest program counter, live flag,
accept flag, input length, coin-window lower endpoint and length, zero and one. -/
def loadReg (dst : Reg) (addr : ℕ) : Micro := .seq (.lit 8 addr) (.read dst 8)
def storeReg (dst : ℕ) (src : Reg) : Micro := .seq (.lit 8 dst) (.write 8 src)

def binaryOp (op : Reg → Reg → Reg → Micro) (d a b : ℕ) : Micro :=
  .seq (loadReg 10 a) (.seq (loadReg 11 b) (.seq (op 12 10 11) (storeReg d 12)))

def coinAt : Micro := .branch 5 10 (.lit 11 2) (.seq (.add 9 4 10)
  (.seq (.coin 11 9) (.branch 11 7 .skip (.lit 11 0))))

def instruction (pc : ℕ) : Instr → Micro
  | .const d c => .seq (.lit 0 (pc+1)) (.seq (.lit 11 c) (storeReg d 11))
  | .add d a b => .seq (.lit 0 (pc+1)) (binaryOp .add d a b)
  | .monus d a b => .seq (.lit 0 (pc+1)) (binaryOp .sub d a b)
  | .load d a => .seq (.lit 0 (pc+1)) (.seq (loadReg 10 a) (.seq (.read 11 10) (storeReg d 11)))
  | .store a b => .seq (.lit 0 (pc+1)) (.seq (loadReg 10 a) (.seq (loadReg 11 b) (.write 10 11)))
  | .jle a b dst => .seq (loadReg 10 a) (.seq (loadReg 11 b) (.branch 10 11 (.lit 0 dst) (.lit 0 (pc+1))))
  | .inputLength d => .seq (.lit 0 (pc+1)) (storeReg d 3)
  | .readInput d a => .seq (.lit 0 (pc+1)) (.seq (loadReg 10 a)
      (.seq (.branch 3 10 (.lit 11 2) (.input 11 10)) (storeReg d 11)))
  | .readCoin d a => .seq (.lit 0 (pc+1)) (.seq (loadReg 10 a) (.seq coinAt (storeReg d 11)))
  | .readWitness d => .seq (.lit 0 (pc+1)) (.seq (.lit 11 2) (storeReg d 11))
  | .query d _ _ => .seq (.lit 0 (pc+1)) (storeReg d 6)
  | .output a => .seq (.lit 0 (pc+1)) (.seq (loadReg 10 a) (.branch 10 6 .skip (.lit 2 1)))
  | .outputBot | .halt => .lit 1 0

structure Represents (st : State) (v : ViewState) (x : List Bool) (base len : ℕ) : Prop where
  mem : v.heap=st.mem
  pc : v.regs 0=st.pc
  live : v.regs 1=(!st.halted).toNat
  answer : v.regs 2=(st.out.contains true).toNat
  input : v.regs 3=x.length
  start : v.regs 4=base
  length : v.regs 5=len
  zero : v.regs 6=0
  one : v.regs 7=1

set_option maxHeartbeats 800000 in
theorem step_correct (Q : Program) (x coins : List Bool) (base len : ℕ) (st : State) (v : ViewState)
    (port : ℕ → ℕ) (input : ∀ i<x.length, port i=bitVal x[i]?) (rep : Represents st v x base len)
    (h : st.halted=false) (i : Instr) (ins : Q[st.pc]?=some i) :
    Represents (Q.step (runTapes x (CoinWindow.window coins base len)) st)
      ((instruction st.pc i).eval port coins v) x base len := by
  obtain ⟨mem,pc,live,answer,dim,start,length,zero,one⟩ := rep
  simp only [h,Bool.not_false,Bool.toNat_true] at live
  have normal (u : ℕ) (hu : x.length ≤ u) : bitVal x[u]?=2 := by simp [List.getElem?_eq_none hu,bitVal]
  have coin (u : ℕ) : bitVal (CoinWindow.window coins base len)[u]? =
    if len ≤ u then 2 else if bitVal coins[base+u]? ≤ 1 then bitVal coins[base+u]? else 0 := by
    rw [CoinWindow.read_window]
    by_cases hit : u<len
    · have no : ¬len ≤ u := by omega
      cases hz : coins[base+u]? with
      | none => simp [hit,no,hz,bitVal]
      | some b => cases b <;> simp [hit,no,hz,bitVal]
    · have hs : len ≤ u := by omega
      simp [hit,hs]
  cases i
  all_goals simp only [Program.step,h,ins,Bool.false_eq_true,if_false]
  all_goals
    simp (config := {zeta := true, maxSteps := 300000}) only [instruction,loadReg,storeReg,binaryOp,coinAt,Micro.eval,
      ViewState.set,ViewState.put,Function.update_self,Function.update_of_ne,mem,dim,start,length,zero,one] 
  all_goals
    first
    | constructor <;> simp (config := {maxSteps := 300000}) [ViewState.set,ViewState.put,Function.update_apply,State.write,
        mem,pc,live,answer,dim,start,length,zero,one,h,coin,runTapes,noOracle,show bitVal none=2 from rfl]
    | skip
  all_goals split_ifs <;> simp (disch := omega) [*,Function.update_apply] <;> rfl

end DirectedHamiltonicity.Main.CycleReduction.Guest

namespace TargetedSamplers.Program

/-- Invalid instruction pointers are fixed points; every genuine step spends at least one unit. -/
theorem fixed_or_pays (P : Program) (τ : Tapes) (s : State) :
    P.step τ s=s ∨ s.work+1 ≤ (P.step τ s).work := by
  by_cases h : s.halted=true
  · exact Or.inl (by simp [step,h])
  · cases ins : P[s.pc]? with
    | none => exact Or.inl (by simp [step,h,ins])
    | some i => right; cases i <;> simp [step,h,ins] <;> omega

private theorem stays {P : Program} {τ : Tapes} {k : ℕ} (same : P.step τ (P.config τ k)=P.config τ k)
    {j : ℕ} (later : k≤j) : P.config τ j = P.config τ k := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le later
  change (P.step τ)^[k+d] State.init = _
  rw [Nat.add_comm,Function.iterate_add_apply]
  exact Function.IsFixedPt.iterate same d

/-- A bound on the public accumulated bit cost is valid as instruction fuel. Running a
bounded subroutine for exactly that many ticks recovers the unique terminal state on any tape. -/
theorem config_at_budget {P : Program} {τ : Tapes} {T : ℕ} {output : Option (List Bool)}
    (bounded : P.RunsIn τ T output) :
    (P.config τ T).halted=true ∧ (P.config τ T).work ≤ T ∧ (P.config τ T).result=output := by
  classical
  obtain ⟨last,eq,work,result⟩ := bounded
  unfold final at eq
  split at eq
  next reaches =>
    let k := Nat.find reaches
    have halt : (P.config τ k).halted=true := Nat.find_spec reaches
    have finish : P.config τ k = last := Option.some.inj eq
    have paid (i : ℕ) (hi : i ≤ k) : i ≤ (P.config τ i).work := by
      induction i with
      | zero => exact Nat.zero_le _
      | succ i ih =>
        have early : i<k := by omega
        have off : ¬(P.config τ i).halted=true := Nat.find_min reaches early
        have stepCost := fixed_or_pays P τ (P.config τ i)
        rcases stepCost with fixed | pay
        · exact (off (by rw [←stays fixed early.le];exact halt)).elim
        · have pre := ih early.le
          change i+1 ≤ ((P.step τ)^[i+1] State.init).work
          rw [Function.iterate_succ_apply']
          exact (Nat.succ_le_succ pre).trans pay
    have room : k≤T := (paid k le_rfl).trans (finish.symm ▸ work)
    have atT := stays (P:=P) (τ:=τ) (k:=k) (by simp [step,halt]) room
    rw [atT]; exact ⟨halt,finish.symm ▸ work,finish.symm ▸ result⟩
  next => contradiction

end TargetedSamplers.Program

namespace DirectedHamiltonicity.Main.CycleReduction

open TargetedSamplers

/-- An executable bounded interpretation of the candidate bit, without an existential halting test. -/
def fuelBit (Q : Program) (T : ℕ) (x coins : List Bool) : Bool :=
  (Q.config (runTapes x coins) T).out.head?.getD false

theorem fuelBit_correct (Q : Program) (A k : ℕ) (time : QueryTime Q A k) {n : ℕ}
    (adj : Fin n → Fin n → Bool) (z : Draw n) (x : List Bool) (valid : candidateInput adj z=some x)
    (coins : List Bool) : fuelBit Q (coinSpan A k n) x coins=outputBit Q x coins := by
  obtain ⟨t,⟨s,found,le,out⟩,budget⟩ := time adj z x valid coins
  have bounded : Q.RunsIn (runTapes x coins) (coinSpan A k n) (some [outputBit Q x coins]) :=
    ⟨s,found,le.trans budget,out⟩
  obtain ⟨_,_,answer⟩ := Program.config_at_budget bounded
  unfold State.result at answer
  split at answer
  · contradiction
  · exact congrArg (fun l : List Bool => l.head?.getD false) (Option.some.inj answer)

end DirectedHamiltonicity.Main.CycleReduction

namespace DirectedHamiltonicity.Main.CycleReduction.Guest

open TargetedSamplers TargetedSamplers.Structured GuestMemory

/-- A finite instruction table. Each test compares with one static instruction address. -/
def dispatch : ℕ → Program → Micro
  | _,[] => .skip
  | p,i::rest => .seq (.lit 13 p) (.branch 0 13 (instruction p i) (dispatch (p+1) rest))

def tick (Q : Program) : Micro := .branch 1 6 .skip (dispatch 0 Q)

private theorem mark {st v x base len} (rep : Represents st v x base len) (z : ℕ) :
    Represents st (v.set 13 z) x base len := by
  obtain ⟨m,pc,h,o,d,p,l,zero,one⟩ := rep
  constructor <;> simp [ViewState.set,Function.update_apply,m,pc,h,o,d,p,l,zero,one]

private theorem dispatch_correct (Q : Program) (x coins : List Bool) (base len : ℕ) (st : State)
    (port : ℕ → ℕ) (input : ∀ i<x.length, port i=bitVal x[i]?) (live : st.halted=false) (code : Program)
    (p : ℕ) (le : p ≤ st.pc) (loc : code[st.pc-p]?=Q[st.pc]?) (v : ViewState) (rep : Represents st v x base len) :
    Represents (Q.step (runTapes x (CoinWindow.window coins base len)) st)
      ((dispatch p code).eval port coins v) x base len := by
  induction code generalizing p v with
  | nil =>
    have missing : Q[st.pc]?=none := by simpa using loc.symm
    simpa [dispatch,Micro.eval,Program.step,live,missing] using rep
  | cons i rest ih =>
    let v' := v.set 13 p
    have rep' : Represents st v' x base len := mark rep p
    have bound : v'.regs 13=p := by simp [v',ViewState.set]
    change Represents _ (if v'.regs 0 ≤ v'.regs 13 then _ else _) _ _ _
    rw [rep'.pc,bound]
    by_cases atPC : st.pc=p
    · rw [if_pos atPC.le]
      have found : Q[st.pc]?=some i := by simpa [atPC] using loc.symm
      have result := step_correct Q x coins base len st v' port input rep' live i found
      rw [show instruction st.pc i=instruction p i from congrArg (fun k => instruction k i) atPC] at result
      change Represents _ ((instruction p i).eval port coins (v.set 13 p)) x base len
      exact result
    · rw [if_neg (by omega)]
      have id : st.pc-p=(st.pc-(p+1))+1 := by omega
      exact ih (p+1) (by omega) (by simpa [id] using loc) v' rep'

theorem tick_correct (Q : Program) (x coins : List Bool) (base len : ℕ) (st : State) (v : ViewState)
    (port : ℕ → ℕ) (input : ∀ i<x.length, port i=bitVal x[i]?) (rep : Represents st v x base len) :
    Represents (Q.step (runTapes x (CoinWindow.window coins base len)) st)
      ((tick Q).eval port coins v) x base len := by
  cases live : st.halted
  · have run := dispatch_correct Q x coins base len st port input live Q 0 (Nat.zero_le _) (by simp) v rep
    simpa only [tick,Micro.eval,rep.live,rep.zero,live,Bool.not_false,Bool.toNat_true,if_neg (by decide : ¬ 1 ≤ 0)] using run
  · simpa [tick,Micro.eval,rep.live,rep.zero,live,Program.step] using rep

/-- Real native execution of a complete simulated step, preserving the input and caller memory banks. -/
theorem native_tick (Q : Program) (x : List Bool) (base len e : ℕ) (τ : Tapes) (st : State) (s : Store)
    (init : Base s e) (input : ∀ i<x.length, s.mem (inputCell i)=bitVal x[i]?)
    (rep : Represents st (snap s e) x base len) :
    let t := ((tick Q).code.run τ s).last
    Base t e ∧ Represents (Q.step (runTapes x (CoinWindow.window τ.coins base len)) st) (snap t e) x base len ∧
      Frame s t := by
  have dyn := (tick Q).correct τ s e init
  refine ⟨dyn.base,?_,dyn.frame⟩
  rw [dyn.state]
  exact tick_correct Q x τ.coins base len st _ _ input rep

/-- Running the same native code repeatedly gives the same finite transcript as the guest, with
arbitrary host tape length and arbitrary pre-existing values in previous guest epochs. -/
theorem native_ticks (Q : Program) (x : List Bool) (base len e : ℕ) (τ : Tapes) (s : Store) (k : ℕ)
    (init : Base s e) (input : ∀ i<x.length, s.mem (inputCell i)=bitVal x[i]?)
    (rep : Represents State.init (snap s e) x base len) :
    let finish := (fun u => ((tick Q).code.run τ u).last)^[k] s
    Base finish e ∧ Represents (Q.config (runTapes x (CoinWindow.window τ.coins base len)) k)
      (snap finish e) x base len ∧ Frame s finish := by
  induction k with
  | zero => exact ⟨init,rep,Frame.refl _⟩
  | succ k ih =>
    let t := (fun u => ((tick Q).code.run τ u).last)^[k] s
    obtain ⟨good,prev,frame⟩ := ih
    have step := native_tick Q x base len e τ _ t good (fun i hi => (frame.input i).trans (input i hi)) prev
    simp only [Program.config,Function.iterate_succ_apply']
    exact ⟨step.1,step.2.1,frame.trans step.2.2⟩

end DirectedHamiltonicity.Main.CycleReduction.Guest

namespace TargetedSamplers.Structured.GuestMemory

/-- Bound just the operands of each executed instruction. The remaining guest cells may hold
larger values. Branches only charge the arm that is actually executed. -/
def Micro.Safe (b : ℕ) (input : ℕ → ℕ) (coins : List Bool) (v : ViewState) : Micro → Prop
  | .skip => True
  | .lit _ z => z.size ≤ b
  | .add _ a c => (v.regs a).size ≤ b ∧ (v.regs c).size ≤ b ∧ (v.regs a+v.regs c).size ≤ b
  | .sub _ a c => (v.regs a).size ≤ b ∧ (v.regs c).size ≤ b ∧ (v.regs a-v.regs c).size ≤ b
  | .read _ a => (v.regs a).size ≤ b ∧ (v.heap (v.regs a)).size ≤ b
  | .write a c => (v.regs a).size ≤ b ∧ (v.regs c).size ≤ b
  | .input _ a => (v.regs a).size ≤ b ∧ (input (v.regs a)).size ≤ b
  | .coin _ a => (v.regs a).size ≤ b
  | .seq x y => x.Safe b input coins v ∧ y.Safe b input coins (x.eval input coins v)
  | .branch a c yes no => (v.regs a).size ≤ b ∧ (v.regs c).size ≤ b ∧
      (if v.regs a ≤ v.regs c then yes.Safe b input coins v else no.Safe b input coins v)

def Micro.nodes : Micro → ℕ
  | .seq x y | .branch _ _ x y => x.nodes+y.nodes+1
  | _ => 1

private theorem reg_size (d : Reg) : (loc d).size ≤ 6 := by
  apply (Nat.size_le_size (show loc d ≤ 63 by unfold loc;have := d.isLt;omega)).trans
  decide

private theorem tape_size (o : Option Bool) : (bitVal o).size ≤ 2 := by
  cases o with | none => decide | some v => cases v <;> decide

private theorem read_bound (d a : Reg) (τ : Tapes) (s : Store) (e pc b : ℕ) (h : Base s e)
    (addr : (s.mem (loc a)).size ≤ b) (word : (view s e (s.mem (loc a))).size ≤ b)
    (ceil : (pc+(Micro.read d a).code.cmd.len+64).size ≤ b) (clk : e.size ≤ b) :
    (Micro.read d a).code.charge τ s pc ≤ 8192*(b+1) := by
  let k := s.mem (loc a)
  let u := s.write 8 k
  let t := (fetch.run τ u).last
  have ub := h.low 8 k (by decide) (by decide) (by decide)
  have eq8 : u.mem 8=k := by simp [u,Store.write]
  have equal : view u e=view s e := low_heap s e 8 k (by decide)
  have fee := fetch_charge τ u (pc+1) k e eq8 ub.clock ub.zero ub.valid
  have viewT := fetch_result τ u e k eq8 ub.clock ub.valid
  have z : t.mem 0=0 := (viewT.2.2 0 (by decide) (by decide) (by decide) (by decide)).trans ub.zero
  have res : t.mem 9=view s e k := viewT.1.trans (congrFun equal k)
  have site : (pc+1+64).size ≤ b := by
    apply (Nat.size_le_size (show pc+1+64 ≤ pc+(Micro.read d a).code.cmd.len+64 by
      simp [Micro.code,Structured.sequence,Fragment.cmd,Cmd.len])).trans ceil
  rw [equal] at fee
  change (s.mem (loc a)).size ≤ b at addr
  have ka : k.size ≤ b := addr
  have val : (view s e k).size ≤ b := word
  have c0 : (0:ℕ).size=0 := rfl
  have c8 : (8:ℕ).size ≤ 7 := by decide
  have c9 : (9:ℕ).size ≤ 7 := by decide
  have cost : (Micro.read d a).code.charge τ s pc =
      (Op.add 8 (loc a) 0).charge τ s+fetch.charge τ u (pc+1)+(Op.add (loc d) 9 0).charge τ t := by
    simp only [Micro.code,Structured.sequence,Fragment.charge,Fragment.run,Fragment.cmd,Cmd.len,Op.eval,h.zero,
      Nat.add_zero,Nat.add_assoc]; rfl
  rw [cost];simp only [Op.charge,h.zero,z,res,Nat.add_zero,c0]
  have := reg_size a;have := reg_size d
  change _ ≤ _;omega

private theorem write_bound (a v : Reg) (τ : Tapes) (s : Store) (e pc b : ℕ) (h : Base s e)
    (addr : (s.mem (loc a)).size ≤ b) (word : (s.mem (loc v)).size ≤ b) (clk : e.size ≤ b) :
    (Micro.write a v).code.charge τ s pc ≤ 8192*(b+1) := by
  let A := s.mem (loc a)
  let W := s.mem (loc v)
  let u := s.write 8 A
  let t := u.write 9 W
  have ua : u.mem (loc v)=W := by simp [u,W,Store.write,show loc v≠8 by unfold loc;omega]
  have uz : u.mem 0=0 := by simp [u,Store.write,h.zero]
  have fee := save_charge τ t (pc+1+1) A e W (by simp [t,u,Store.write]) (by simp [t,u,Store.write,h.clock])
    (by simp [t,Store.write])
  have c0 : (0:ℕ).size=0 := rfl
  have c8 : (8:ℕ).size ≤ 7 := by decide
  have c9 : (9:ℕ).size ≤ 7 := by decide
  have cost : (Micro.write a v).code.charge τ s pc =
      (Op.add 8 (loc a) 0).charge τ s + (Op.add 9 (loc v) 0).charge τ u + save.charge τ t (pc+1+1) := by
    simp only [Micro.code,Structured.sequence,Fragment.charge,Fragment.run,Fragment.cmd,Cmd.len,Op.eval,h.zero,Nat.add_zero]
    change _+(_+(save.charge τ (u.write 9 (u.mem (loc v)+u.mem 0)) _+0))=_
    rw [ua,uz,Nat.add_zero]; simp only [Nat.add_zero,Nat.add_assoc]; rfl
  rw [cost];simp only [Op.charge,h.zero,uz,ua,Nat.add_zero,c0]
  have := reg_size a;have := reg_size v
  dsimp only [A,W] at fee ⊢
  omega

private theorem input_bound (d a : Reg) (τ : Tapes) (s : Store) (pc b : ℕ)
    (addr : (s.mem (loc a)).size ≤ b) (word : (s.mem (inputCell (s.mem (loc a)))).size ≤ b) :
    (Micro.input d a).code.charge τ s pc ≤ 8192*(b+1) := by
  let k := s.mem (loc a)
  have form : k+k+(k+k)+66=inputCell k := by unfold inputCell tag;ring
  have limit : (inputCell k).size ≤ k.size+7 := by
    apply Nat.size_le.mpr
    rw [pow_add];have := Nat.lt_size_self k;have := Nat.two_pow_pos k.size
    unfold inputCell tag;norm_num;omega
  have b1 := (Nat.size_le_size (show k+k ≤ inputCell k by unfold inputCell tag;omega)).trans limit
  have b2 := (Nat.size_le_size (show k+k+(k+k) ≤ inputCell k by unfold inputCell tag;omega)).trans limit
  have c8 : (8:ℕ).size ≤ 7 := by decide
  have c11 : (11:ℕ).size ≤ 7 := by decide
  have c66 : (66:ℕ).size ≤ 7 := by decide
  have := reg_size a;have := reg_size d
  have high : 64 ≤ inputCell k := by unfold inputCell tag;omega
  unfold k at form limit b1 b2 high
  simp (disch := omega) [Micro.code,Structured.sequence,Fragment.charge,Fragment.run,Op.charge,Op.eval,Store.write,
    Function.update_apply,form]
  omega


/-- Uniform linear overhead in the number of touched bits. The syntactic constant depends
only on the finite macro sequence, and independent guest registers need no size bound. -/
theorem Micro.cost_bound (m : Micro) (τ : Tapes) (s : Store) (e pc b : ℕ) (h : Base s e)
    (clk : e.size ≤ b) (site : (pc+m.code.cmd.len+64).size ≤ b)
    (safe : m.Safe b (fun i => s.mem (inputCell i)) τ.coins (snap s e)) :
    m.code.charge τ s pc ≤ m.nodes*(8192*(b+1)) := by
  induction m generalizing pc s with
  | skip => simp [code,Fragment.charge,nodes]
  | lit d z =>
    have rd := reg_size d
    change z.size ≤ b at safe
    simp only [code,Fragment.charge,Op.charge,nodes,Nat.one_mul];omega
  | add d a c =>
    have rd := reg_size d;have ra := reg_size a;have rc := reg_size c
    obtain ⟨wa,wc,wd⟩ := safe
    change (s.mem (loc a)).size ≤ b at wa
    change (s.mem (loc c)).size ≤ b at wc
    change (s.mem (loc a)+s.mem (loc c)).size ≤ b at wd
    simp only [code,Fragment.charge,Op.charge,nodes,Nat.one_mul];omega
  | sub d a c =>
    have rd := reg_size d;have ra := reg_size a;have rc := reg_size c
    obtain ⟨wa,wc,wd⟩ := safe
    change (s.mem (loc a)).size ≤ b at wa
    change (s.mem (loc c)).size ≤ b at wc
    change (s.mem (loc a)-s.mem (loc c)).size ≤ b at wd
    simp only [code,Fragment.charge,Op.charge,nodes,Nat.one_mul];omega
  | coin d a =>
    have rd := reg_size d;have ra := reg_size a;have out := tape_size (τ.coins[s.mem (loc a)]?)
    change (s.mem (loc a)).size ≤ b at safe
    simp only [code,Fragment.charge,Op.charge,nodes,Nat.one_mul];omega
  | read d a => simpa only [nodes,Nat.one_mul] using read_bound d a τ s e pc b h safe.1 safe.2 site clk
  | write a v => simpa only [nodes,Nat.one_mul] using write_bound a v τ s e pc b h safe.1 safe.2 clk
  | input d a => simpa only [nodes,Nat.one_mul] using input_bound d a τ s pc b safe.1 safe.2
  | seq x y ix iy =>
    let u := (x.code.run τ s).last
    have first := x.correct τ s e h
    have xsite : (pc+x.code.cmd.len+64).size ≤ b := (Nat.size_le_size
      (show _ ≤ pc+(Micro.seq x y).code.cmd.len+64 by simp only [code,Fragment.cmd,Cmd.len];omega)).trans site
    have ysite : (pc+x.code.cmd.len+y.code.cmd.len+64).size ≤ b := by
      simpa only [code,Fragment.cmd,Cmd.len,Nat.add_assoc] using site
    have xs := ix s pc h xsite safe.1
    have ys := iy u (pc+x.code.cmd.len) first.base ysite (by rw [first.state,funext first.frame.input];exact safe.2)
    change x.code.charge τ s pc+y.code.charge τ u _ ≤ _
    simp only [nodes,Nat.add_mul,Nat.one_mul];omega
  | branch a c y n iy ino =>
    let yy := pc+1+n.code.cmd.len+1
    have upper : (pc+(Micro.branch a c y n).code.cmd.len+64).size ≤ b := site
    have here (z : ℕ) (hz : z ≤ pc+(Micro.branch a c y n).code.cmd.len+64) :
        z.size ≤ b := (Nat.size_le_size hz).trans upper
    have py := here (yy+y.code.cmd.len+64) (by dsimp [yy,code,Fragment.cmd,Cmd.len];omega)
    have pn := here (pc+1+n.code.cmd.len+64) (by dsimp [code,Fragment.cmd,Cmd.len];omega)
    have g := here yy (by dsimp [yy,code,Fragment.cmd,Cmd.len];omega)
    have j := here (yy+y.code.cmd.len) (by dsimp [yy,code,Fragment.cmd,Cmd.len];omega)
    obtain ⟨pa,pb,chosen⟩ := safe
    change (s.mem (loc a)).size ≤ b at pa
    change (s.mem (loc c)).size ≤ b at pb
    have ra := reg_size a;have rc := reg_size c
    have test : testCharge s (loc a) (loc c) yy ≤ 4*(b+8) := by unfold testCharge;omega
    by_cases take : s.mem (loc a) ≤ s.mem (loc c)
    · have cond : (snap s e).regs a ≤ (snap s e).regs c := take
      rw [if_pos cond] at chosen
      have cost := iy s yy h py chosen
      simp only [code,Fragment.charge,if_pos take,nodes,Nat.add_mul,Nat.one_mul]
      change testCharge s (loc a) (loc c) yy+y.code.charge τ s yy ≤ _
      omega
    · have cond : ¬ (snap s e).regs a ≤ (snap s e).regs c := take
      rw [if_neg cond] at chosen
      have cost := ino s (pc+1) h pn chosen
      have good := (n.correct τ s e h).base
      have jump : testCharge (n.code.run τ s).last 0 0 (yy+y.code.cmd.len) ≤ b+1 := by
        simp [testCharge,good.zero];omega
      simp only [code,Fragment.charge,if_neg take,nodes,Nat.add_mul,Nat.one_mul]
      change testCharge s (loc a) (loc c) yy+(n.code.charge τ s (pc+1)+testCharge _ 0 0 (yy+y.code.cmd.len)) ≤ _
      omega

end TargetedSamplers.Structured.GuestMemory

namespace DirectedHamiltonicity.Main.CycleReduction.Guest

open TargetedSamplers TargetedSamplers.Structured GuestMemory

/-- The numeric instruction fields are constants of the guest program. -/
def fields : Instr → ℕ
  | .const x y | .load x y | .store x y | .readInput x y | .readCoin x y => x+y
  | .add x y z | .monus x y z | .jle x y z | .query x y z => x+y+z
  | .inputLength x | .readWitness x | .output x => x
  | .outputBot | .halt => 0

def static (Q : Program) := 64+Q.length+(Q.map fields).sum

private theorem small (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self

private theorem sum_width (a b : ℕ) : (a+b).size ≤ a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a;have hb := Nat.lt_size_self b
  have pa := Nat.two_pow_pos a.size;have pb := Nat.two_pow_pos b.size
  rw [pow_succ,pow_add];nlinarith only [ha,hb,Nat.mul_le_mul_left (2^a.size) pb,Nat.mul_le_mul_right (2^b.size) pa]

private theorem field_le {Q : Program} {i : Instr} (member : i ∈ Q) : fields i ≤ static Q := by
  have inc : fields i ≤ (Q.map fields).sum := List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨i,member,rfl⟩)
  unfold static;omega

def delta (Q : Program) (τ : Tapes) (st : State) := (Q.step τ st).work-st.work

set_option maxHeartbeats 1300000 in
theorem instruction_safe (Q : Program) (x coins : List Bool) (base len : ℕ) (st : State) (v : ViewState)
    (port : ℕ → ℕ) (input : ∀ i<x.length, port i=bitVal x[i]?) (rep : Represents st v x base len)
    (live : st.halted=false) (i : Instr) (ins : Q[st.pc]?=some i) (b : ℕ)
    (room : 10+fields i+(st.pc+1)+x.length.size+base.size+len.size+
      delta Q (runTapes x (CoinWindow.window coins base len)) st ≤ b) :
    (instruction st.pc i).Safe b port coins v := by
  obtain ⟨mem,pc,h,out,dim,offset,length,zero,one⟩ := rep
  have symbol (bits : List Bool) (j : ℕ) : (bitVal bits[j]?).size ≤ 2 := by
    cases bits[j]? with | none => decide | some bv => cases bv <;> decide
  have nativeInput (u : ℕ) (h : u<x.length) : (port u).size ≤ 2 := by rw [input u h]; exact symbol x u
  have pcWidth := small (st.pc+1)
  have c2 : (2:ℕ).size=2 := rfl
  have c1 : (1:ℕ).size=1 := rfl
  have c0 : (0:ℕ).size=0 := rfl
  cases i
  all_goals
    simp only [delta,Program.step,live,Bool.false_eq_true,if_false,ins,fields,State.write,runTapes] at room
    simp only [instruction,binaryOp,loadReg,storeReg,coinAt,Micro.Safe,Micro.eval,ViewState.set,ViewState.put,
      Function.update_self,Function.update_of_ne,mem,zero,one,dim,offset,length]
  all_goals
    first
    | (rename_i d a;have addrWidth := sum_width base (st.mem a);have portWidth := nativeInput (st.mem a);
       have coinWidth := symbol coins (base+st.mem a);have sd := small d;have sa := small a;
       split_ifs <;> simp_all [Function.update_apply] <;> omega)
    | (split_ifs <;> simp_all [Function.update_apply] <;> omega)
    | (simp_all [Function.update_apply] <;> omega)
    | skip
  case readCoin d a =>
    have sa := small a
    have sd := small d
    have sizeA := sum_width base (st.mem a)
    have sizeB := symbol coins (base+st.mem a)
    by_cases past : len ≤ st.mem a <;> by_cases bit : bitVal coins[base+st.mem a]? ≤ 1 <;>
      simp [Function.update_apply,offset,length,one,zero,mem,past,bit,c2,c0,c1] <;> omega

theorem bounded_pc (Q : Program) (τ : Tapes) (j : ℕ) : (Q.config τ j).pc ≤ static Q+1 := by
  induction j with
  | zero => simp [Program.config,State.init]
  | succ j ih =>
    let st := Q.config τ j
    change ((Q.step τ)^[j+1] State.init).pc ≤ _
    rw [Function.iterate_succ_apply']
    change (Q.step τ st).pc ≤ _
    change st.pc ≤ _ at ih
    cases live : st.halted with
    | true => simpa [Program.step,live] using ih
    | false =>
      cases ins : Q[st.pc]? with
      | none => simpa [Program.step,live,ins] using ih
      | some i =>
        have addr : st.pc<Q.length := by
          by_contra! bad
          rw [List.getElem?_eq_none bad] at ins;contradiction
        have bound := field_le (List.mem_of_getElem? ins)
        have lenQ : Q.length ≤ static Q := by unfold static;omega
        cases i <;> simp_all [Program.step,fields] <;> (try split_ifs) <;> omega

def overhead (Q : Program) (x : List Bool) (base len e pc : ℕ) :=
  50+2*static Q+x.length.size+base.size+len.size+e.size+
    (pc+(tick Q).code.cmd.len+64).size

private theorem dispatch_safe (Q : Program) (x coins : List Bool) (base len : ℕ) (st : State) (port : ℕ → ℕ)
    (input : ∀ i<x.length, port i=bitVal x[i]?) (live : st.halted=false) (code : Program) (p : ℕ)
    (pos : p ≤ st.pc) (site : p+code.length ≤ Q.length) (pcBound : st.pc ≤ static Q+1)
    (lookup : code[st.pc-p]?=Q[st.pc]?) (v : ViewState) (rep : Represents st v x base len) (b : ℕ)
    (budget : 50+2*static Q+x.length.size+base.size+len.size+delta Q (runTapes x (CoinWindow.window coins base len)) st ≤ b) :
    (dispatch p code).Safe b port coins v := by
  induction code generalizing p v with
  | nil => trivial
  | cons i tail ih =>
    let v' := v.set 13 p
    have rp : Represents st v' x base len := by
      obtain ⟨m,pc,h,o,d,p,l,z,one⟩ := rep
      constructor <;> simp [v',ViewState.set,Function.update_apply,m,pc,h,o,d,p,l,z,one]
    have t : v'.regs 13=p := by simp [v',ViewState.set]
    have lenQ : Q.length ≤ static Q := by unfold static;omega
    have ps := small p
    have pB := small st.pc
    simp only [List.length_cons] at site
    change p.size ≤ b ∧ (v'.regs 0).size ≤ b ∧ _ 
    refine ⟨by omega,?_,?_,?_⟩
    · rw [rp.pc];omega
    · change (v'.regs 13).size ≤ b;rw [t];omega
    · change (if v'.regs 0 ≤ v'.regs 13 then _ else _)
      rw [rp.pc,t]
      by_cases here : st.pc=p
      · rw [if_pos here.le]
        have found : Q[st.pc]?=some i := by simpa [here] using lookup.symm
        have fi := field_le (List.mem_of_getElem? found)
        have safe := instruction_safe Q x coins base len st v' port input rp live i found b (by omega)
        rw [show instruction st.pc i=instruction p i from congrArg (fun j => instruction j i) here] at safe
        exact safe
      · rw [if_neg (by omega)]
        have id : st.pc-p=(st.pc-(p+1))+1 := by omega
        exact ih (p+1) (by omega) (by omega) (by simpa [id] using lookup) v' rp

theorem tick_charge (Q : Program) (x : List Bool) (base len e pc : ℕ) (τ : Tapes) (s : Store) (st : State)
    (h : Base s e) (input : ∀ i<x.length, s.mem (inputCell i)=bitVal x[i]?)
    (rep : Represents st (snap s e) x base len) (pcBound : st.pc ≤ static Q+1) :
    (tick Q).code.charge τ s pc ≤ (tick Q).nodes*8192*
      (overhead Q x base len e pc+delta Q (runTapes x (CoinWindow.window τ.coins base len)) st+1) := by
  let b := overhead Q x base len e pc+delta Q (runTapes x (CoinWindow.window τ.coins base len)) st
  have large : 50+2*static Q+x.length.size+base.size+len.size+
      delta Q (runTapes x (CoinWindow.window τ.coins base len)) st ≤ b := by dsimp [b,overhead];omega
  have enough : (tick Q).Safe b (fun i => s.mem (inputCell i)) τ.coins (snap s e) := by
    change ((snap s e).regs 1).size ≤ b ∧ ((snap s e).regs 6).size ≤ b ∧ _
    cases live : st.halted with
    | true => simp [tick,Micro.Safe,rep.live,rep.zero,live]
    | false =>
      have body := dispatch_safe Q x τ.coins base len st _ input live Q 0 (Nat.zero_le _) (by simp)
        pcBound (by simp) _ rep b large
      simpa [tick,Micro.Safe,rep.live,rep.zero,live,show 1 ≤ b by omega] using body
  have result := (tick Q).cost_bound τ s e pc b h (by dsimp [b,overhead];omega)
    (by dsimp [b,overhead];omega) enough
  simpa only [b,Nat.mul_assoc] using result

end DirectedHamiltonicity.Main.CycleReduction.Guest

namespace DirectedHamiltonicity.Main.CycleReduction.Guest

open TargetedSamplers TargetedSamplers.Structured GuestMemory

/-- Registers in the caller bank other than the private fuel counter survive a call. -/
structure Preserves (s t : Store) : Prop where
  output : t.out=s.out
  input : ∀ i, t.mem (inputCell i)=s.mem (inputCell i)
  caller : ∀ i, i≠0 → t.mem (callerCell i)=s.mem (callerCell i)

theorem Preserves.refl (s : Store) : Preserves s s := ⟨rfl,fun _ => rfl,fun _ _ => rfl⟩
theorem Preserves.trans {s t u : Store} (p : Preserves s t) (q : Preserves t u) : Preserves s u :=
  ⟨q.output.trans p.output,fun i => (q.input i).trans (p.input i),
    fun i h => (q.caller i h).trans (p.caller i h)⟩
theorem preserves_frame {s t : Store} (f : Frame s t) : Preserves s t :=
  ⟨f.output,f.input,fun i _ => f.caller i⟩

private theorem write_fuel (s : Store) (e k : ℕ) (good : Base s e) :
    let t := s.write (callerCell 0) k
    Base t e ∧ snap t e=snap s e ∧ Preserves s t ∧ t.mem (callerCell 0)=k := by
  have high : callerCell 0=67 := rfl
  have tag_ne (i : ℕ) : tag i ≠ 67 := by unfold tag;omega
  have val_ne (i : ℕ) : value i ≠ 67 := by unfold value tag;omega
  have reg_ne (r : Reg) : loc r ≠ 67 := by unfold loc;have := r.isLt;omega
  have input_ne (i : ℕ) : inputCell i ≠ 67 := by unfold inputCell tag;omega
  have caller_ne (i : ℕ) (h : i≠0) : callerCell i ≠ 67 := by unfold callerCell tag;omega
  rw [high]
  refine ⟨⟨by simpa [Store.write] using good.zero,by simpa [Store.write] using good.clock,
    fun i => by simpa [Store.write,tag_ne] using good.valid i⟩,?_,?_,by simp [Store.write]⟩
  · have heap : view (s.write 67 k) e=view s e := by
      funext i;simp [view,Store.write,tag_ne,val_ne]
    unfold snap;rw [heap];simp [Store.write,Function.update_of_ne,reg_ne]
  · exact ⟨rfl,fun i => by simp [Store.write,input_ne],fun i hi => by simp [Store.write,caller_ne i hi]⟩

def decrement := Op.sub (callerCell 0) (callerCell 0) (callerCell 1)
def body (Q : Program) := Cmd.seq (tick Q).code.cmd (.op decrement)
def interpreter (Q : Program) := Cmd.whileGt (callerCell 0) 0 (body Q)

def runWidth (Q : Program) (x : List Bool) (base len e pc T : ℕ) :=
  100 + overhead Q x base len e (pc+1) + (pc+1+(body Q).len+1).size + T.size

def factor (Q : Program) := (tick Q).nodes*8192+64

private theorem mono_step (Q : Program) (τ : Tapes) (st : State) : st.work ≤ (Q.step τ st).work := by
  rcases Program.fixed_or_pays Q τ st with eq|le
  · rw [eq]
  · omega

private theorem config_succ (Q : Program) (τ : Tapes) (j : ℕ) :
    Q.config τ (j+1)=Q.step τ (Q.config τ j) := by
  exact Function.iterate_succ_apply' ..

private theorem mono_config (Q : Program) (τ : Tapes) (i j : ℕ) (le : i≤j) :
    (Q.config τ i).work ≤ (Q.config τ j).work := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le le
  induction d with
  | zero => exact le_rfl
  | succ d ih => rw [←Nat.add_assoc,config_succ];exact (ih (by omega)).trans (mono_step ..)

/-- Native execution of a finite fuel loop. The bit costs of guest instructions telescope,
so an exponential bound on the guest's bit time is incurred only once per invocation. -/
theorem interpreter_runs (Q P : Program) (x : List Bool) (base len e pc T : ℕ) (τ : Tapes)
    (sub : Contains P pc ((interpreter Q).compile pc)) (k j : ℕ) (s : Store) (st : State)
    (fit : k≤T) (atPC : Located st pc s) (good : Base s e)
    (input : ∀ i<x.length, s.mem (inputCell i)=bitVal x[i]?)
    (one : s.mem (callerCell 1)=1) (fuel : s.mem (callerCell 0)=k)
    (rep : Represents (Q.config (runTapes x (CoinWindow.window τ.coins base len)) j) (snap s e) x base len) :
    let guest := runTapes x (CoinWindow.window τ.coins base len)
    ∃ (u : State) (t : Store) (steps fee : ℕ), Travels P τ st u steps fee ∧
      Located u (pc+(interpreter Q).len) t ∧ Base t e ∧ Preserves s t ∧
      Represents (Q.config guest (j+k)) (snap t e) x base len ∧
      fee ≤ factor Q * ((k+1)*runWidth Q x base len e pc T + ((Q.config guest (j+k)).work-(Q.config guest j).work)) := by
  let guest := runTapes x (CoinWindow.window τ.coins base len)
  let W := runWidth Q x base len e pc T
  let N := (tick Q).nodes*8192
  let K := factor Q
  have go := loop_sites sub
  have stopPC : pc+(interpreter Q).len=pc+1+(body Q).len+1 := by simp [interpreter,Cmd.len,Nat.add_assoc]
  have Wpos : 0<W := by dsimp [W,runWidth];omega
  have Kpos : 1≤K := by dsimp [K,factor];omega
  induction k generalizing j s st with
  | zero =>
    have test := test_travels (τ:=τ) atPC _ _ _ go.1
    have stop := step_jle τ atPC _ _ _ go.1
    rw [if_pos (by rw [fuel];omega),←stopPC] at stop
    refine ⟨_,s,1,_,test,stop,good,Preserves.refl s,by simpa using rep,?_⟩
    have fee : testCharge s (callerCell 0) 0 (pc+1+(body Q).len+1) ≤ W := by
      simp only [testCharge,fuel,good.zero];dsimp [W,runWidth];change 1+7+0+0+0+_ ≤ _;omega
    simpa [K,W] using fee.trans (Nat.le_mul_of_pos_left W Kpos)
  | succ k ih =>
    let g := Q.config guest j
    let nxt := Q.config guest (j+1)
    let post := ((tick Q).code.run τ s).last
    let after := post.write (callerCell 0) k
    let edge := delta Q guest g
    have num : g.work ≤ nxt.work := by dsimp [g,nxt];rw [config_succ];exact mono_step ..
    have ed : edge=nxt.work-g.work := by dsimp [edge,delta,nxt,g];rw [config_succ]
    have start := step_jle τ atPC _ _ _ go.1
    rw [if_neg (by rw [fuel,good.zero];omega)] at start
    have guard := test_travels (τ:=τ) atPC _ _ _ go.1
    have site : Contains P (pc+1) ((tick Q).code.cmd.compile (pc+1)) := go.2.1.left
    have dec : P[pc+1+(tick Q).code.cmd.len]?=some decrement.instruction := by simpa using go.2.1.right.one
    obtain ⟨mid,journey,atMid⟩ := (tick Q).code.compile_charge P τ (pc+1) _ s site start
    obtain ⟨pbase,prep,frame⟩ := native_tick Q x base len e τ g s good input rep
    change Base post e at pbase
    have pone : post.mem (callerCell 1)=1 := (frame.caller 1).trans one
    have pfuel : post.mem (callerCell 0)=k+1 := (frame.caller 0).trans fuel
    have decState : decrement.eval τ post=after := by simp [decrement,Op.eval,pfuel,pone,after]
    have atDec := step_op τ atMid decrement dec
    have payDec := op_travels (τ:=τ) atMid decrement dec
    rw [decState] at atDec
    have midPC : pc+1+(tick Q).code.cmd.len+1=pc+1+(body Q).len := by simp [body,Cmd.len,Nat.add_assoc]
    rw [midPC] at atDec
    have back := step_jump τ atDec _ go.2.2
    have payBack := test_travels (τ:=τ) atDec 0 0 pc go.2.2
    obtain ⟨abase,asnap,aframe,afuel⟩ := write_fuel post e k pbase
    have preFrame : Preserves s after := (preserves_frame frame).trans aframe
    have arep : Represents nxt (snap after e) x base len := by rw [asnap];simpa only [nxt,config_succ] using prep
    obtain ⟨u,t,steps,fee,rest,located,goodEnd,pres,endRep,budget⟩ :=
      ih (j+1) after _ (by omega) back abase (fun i h => (preFrame.input i).trans (input i h))
        ((preFrame.caller 1 (by decide)).trans one) afuel arep
    have index : j+1+k=j+(k+1) := by omega
    rw [index] at endRep budget
    refine ⟨u,t,_,_,(((guard.trans journey).trans payDec).trans payBack).trans rest,located,goodEnd,
      preFrame.trans pres,endRep,?_⟩
    have bTick := tick_charge Q x base len e (pc+1) τ s g good input rep (bounded_pc Q guest j)
    change (tick Q).code.charge τ s (pc+1) ≤ N*(overhead Q x base len e (pc+1)+edge+1) at bTick
    have cap : overhead Q x base len e (pc+1)+edge+1 ≤ W+edge := by dsimp [W,runWidth];omega
    have kernel := bTick.trans (Nat.mul_le_mul_left N cap)
    have stopSize := Nat.size_le_size (show pc≤pc+1+(body Q).len+1 by omega)
    have ctr := Nat.size_le_size fit
    have smaller := Nat.size_le_size (show k≤T by omega)
    have guardCost : testCharge s (callerCell 0) 0 (pc+1+(body Q).len+1) ≤ 4*W := by
      simp only [testCharge,fuel,good.zero];dsimp [W,runWidth];change 1+7+0+_+0+_ ≤ _;omega
    have decCost : decrement.charge τ post ≤ 4*W := by
      simp only [decrement,Op.charge,pfuel,pone,Nat.add_sub_cancel];dsimp [W,runWidth]
      change 1+7+7+7+_+1+k.size ≤ _;omega
    have backCost : testCharge after 0 0 pc ≤ 4*W := by
      have az : after.mem 0=0 := abase.zero
      simp only [testCharge,az];dsimp [W,runWidth];change 1+0+0+0+0+_ ≤ _;omega
    have overheadCost : 4*W+4*W+4*W ≤ 64*(W+edge) := by omega
    have stepCost : testCharge s (callerCell 0) 0 (pc+1+(body Q).len+1) + (tick Q).code.charge τ s (pc+1) +
        decrement.charge τ post + testCharge after 0 0 pc ≤ K*(W+edge) := by
      change _ ≤ (N+64)*(W+edge)
      rw [Nat.add_mul];omega
    let last := Q.config guest (j+(k+1))
    have later : nxt.work ≤ last.work := mono_config Q guest (j+1) (j+(k+1)) (by omega)
    have diff : edge+(last.work-nxt.work)=last.work-g.work := by omega
    change fee ≤ K*((k+1)*W+(last.work-nxt.work)) at budget
    change _ + fee ≤ K*((k+1+1)*W+(last.work-g.work))
    calc
      _ ≤ K*(W+edge) + K*((k+1)*W+(last.work-nxt.work)) := Nat.add_le_add stepCost budget
      _ = K*((k+1+1)*W+(last.work-g.work)) := by
        rw [←Nat.mul_add,show (k+1+1)*W=(k+1)*W+W by ring];congr 1;omega

end DirectedHamiltonicity.Main.CycleReduction.Guest

namespace DirectedHamiltonicity.Main.CycleReduction.Guest

open TargetedSamplers TargetedSamplers.Structured GuestMemory

/-- Caller cells 0 through 4 contain the fuel, one, input length, coin offset and coin length.
Only the guest epoch and fixed scratch registers are initialized. -/
def setup : Fragment := Structured.sequence [
  .op (.const (loc 7) 1),.op (.add 10 10 (loc 7)),.op (.const (loc 0) 0),
  .op (.const (loc 1) 1),.op (.const (loc 2) 0),.op (.add (loc 3) (callerCell 2) 0),
  .op (.add (loc 4) (callerCell 3) 0),.op (.add (loc 5) (callerCell 4) 0),.op (.const (loc 6) 0)]

def call (Q : Program) := Cmd.seq setup.cmd (interpreter Q)

set_option maxHeartbeats 2000000 in
/-- An invocation with a fresh epoch begins with the exact all-zero memory of the guest. -/
theorem setup_ok (τ : Tapes) (s : Store) (e base len : ℕ) (x : List Bool) (h : Base s e)
    (dim : s.mem (callerCell 2)=x.length) (offset : s.mem (callerCell 3)=base) (length : s.mem (callerCell 4)=len) :
    let t := (setup.run τ s).last
    Base t (e+1) ∧ Frame s t ∧ Represents State.init (snap t (e+1)) x base len := by
  let t := (setup.run τ s).last
  have high (a : ℕ) (ha : 64≤a) : t.mem a = s.mem a := by
    simp (disch := omega) [t,setup,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,loc]
  have clock : t.mem 10=e+1 := by
    simp [t,setup,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,loc,h.clock]
  have base0 : t.mem 0=0 := by
    simp [t,setup,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,loc,h.zero]
  have heap : view t (e+1)=fun _ => 0 := by
    funext a
    have equal : view t (e+1) a=view s (e+1) a := by
      simp only [view,high (tag a) (by unfold tag;omega),high (value a) (by unfold value tag;omega)]
    exact equal.trans (congrFun (next_empty h.valid) a)
  have regs (r : Reg) : (snap t (e+1)).regs r=t.mem (loc r) := rfl
  have dc : s.mem 75=x.length := dim
  have ofst : s.mem 79=base := offset
  have ln : s.mem 83=len := length
  refine ⟨⟨base0,clock,fun i => (high (tag i) (by unfold tag;omega)).symm ▸ (h.valid i).trans (by omega)⟩,
    ⟨rfl,fun i => high _ (by unfold inputCell tag;omega),fun i => high _ (by unfold callerCell tag;omega)⟩,?_⟩
  constructor
  · exact heap
  all_goals
    simp [regs,t,setup,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,loc,callerCell,
      tag,snap,State.init,h.zero,dc,ofst,ln]

theorem setup_fee (τ : Tapes) (s : Store) (e base len pc : ℕ) (x : List Bool) (h : Base s e)
    (dim : s.mem (callerCell 2)=x.length) (offset : s.mem (callerCell 3)=base) (length : s.mem (callerCell 4)=len) :
    setup.charge τ s pc ≤ 1024*(1+(e+1).size+e.size+x.length.size+base.size+len.size) := by
  have dc : s.mem 75=x.length := dim
  have ofst : s.mem 79=base := offset
  have ln : s.mem 83=len := length
  simp [setup,Structured.sequence,Fragment.charge,Fragment.run,Op.charge,Op.eval,Store.write,Function.update_apply,
    loc,callerCell,tag,h.clock,h.zero,dc,ofst,ln]
  have small (i : ℕ) (b : i ≤ 128) : i.size ≤ 8 := (Nat.size_le_size b).trans (by decide)
  have h27 := small 27 (by decide)
  have h10 := small 10 (by decide)
  have h20 := small 20 (by decide)
  have h21 := small 21 (by decide)
  have h22 := small 22 (by decide)
  have h23 := small 23 (by decide)
  have h75 := small 75 (by decide)
  have h24 := small 24 (by decide)
  have h79 := small 79 (by decide)
  have h25 := small 25 (by decide)
  have h83 := small 83 (by decide)
  have h26 := small 26 (by decide)
  omega

def allowance (Q : Program) (x : List Bool) (base len e pc T : ℕ) :=
  1024*(1+(e+1).size+e.size+x.length.size+base.size+len.size) +
    factor Q*((T+1)*runWidth Q x base len (e+1) (pc+setup.cmd.len) T+T)

/-- A relocatable, fixed native subroutine returning the guest's sole output bit, with a fresh
empty guest heap on every call and random access to the designated virtual tapes. -/
theorem call_runs (Q P : Program) (x : List Bool) (base len e pc T : ℕ) (τ : Tapes)
    (s : Store) (st : State) (v : Bool) (time : Q.RunsIn (runTapes x (CoinWindow.window τ.coins base len)) T (some [v]))
    (sub : Contains P pc ((call Q).compile pc)) (atPC : Located st pc s) (good : Base s e)
    (input : ∀ i<x.length, s.mem (inputCell i)=bitVal x[i]?)
    (one : s.mem (callerCell 1)=1) (fuel : s.mem (callerCell 0)=T)
    (dim : s.mem (callerCell 2)=x.length) (offset : s.mem (callerCell 3)=base) (length : s.mem (callerCell 4)=len) :
    ∃ (u : State) (t : Store) (steps fee : ℕ), Travels P τ st u steps fee ∧
      Located u (pc+(call Q).len) t ∧ Base t (e+1) ∧ Preserves s t ∧
      t.mem (loc 2)=v.toNat ∧ fee ≤ allowance Q x base len e pc T := by
  let t := (setup.run τ s).last
  let guest := runTapes x (CoinWindow.window τ.coins base len)
  obtain ⟨m,moves,start⟩ := setup.compile_charge P τ pc st s sub.left atPC
  obtain ⟨tb,tf,rep⟩ := setup_ok τ s e base len x good dim offset length
  have loopSite : Contains P (pc+setup.cmd.len) ((interpreter Q).compile (pc+setup.cmd.len)) := by simpa using sub.right
  obtain ⟨u,z,steps,fee,go,last,baseEnd,frame,out,bound⟩ :=
    interpreter_runs Q P x base len (e+1) (pc+setup.cmd.len) T τ loopSite T 0 t m le_rfl start tb
      (fun i hi => (tf.input i).trans (input i hi)) ((tf.caller 1).trans one) ((tf.caller 0).trans fuel) rep
  obtain ⟨_,paid,result⟩ := Program.config_at_budget time
  change (Q.config guest T).result=some [v] at result
  have word : (Q.config guest T).out=[v] := by
    unfold State.result at result
    split at result
    · contradiction
    · exact Option.some.inj result
  have answer := out.answer
  change z.mem (loc 2)=((Q.config guest (0+T)).out.contains true).toNat at answer
  simp only [Nat.zero_add,word] at answer
  have bit : ([v].contains true).toNat=v.toNat := by cases v <;> rfl
  have gCost : (Q.config guest T).work ≤ T := paid
  simp only [Nat.zero_add] at bound
  have subCost : (Q.config guest T).work-(Q.config guest 0).work ≤ T :=
    (Nat.sub_le _ _).trans gCost
  refine ⟨u,z,_,_,moves.trans go,by simpa [call,Cmd.len,Nat.add_assoc] using last,baseEnd,
    (preserves_frame tf).trans frame,answer.trans bit,?_⟩
  apply Nat.add_le_add (setup_fee τ s e base len pc x good dim offset length)
  exact bound.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left subCost _))

end DirectedHamiltonicity.Main.CycleReduction.Guest

namespace DirectedHamiltonicity.Main.CycleReduction.Guest

open TargetedSamplers TargetedSamplers.Structured GuestMemory

private theorem size_add (a b : ℕ) : (a+b).size ≤ a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a;have hb := Nat.lt_size_self b
  have pa := Nat.two_pow_pos a.size;have pb := Nat.two_pow_pos b.size
  rw [pow_succ,pow_add];nlinarith only [ha,hb,Nat.mul_le_mul_left (2^a.size) pb,Nat.mul_le_mul_right (2^b.size) pa]

def callSize (Q : Program) := setup.cmd.len+(tick Q).code.cmd.len+(body Q).len+70
def widthFactor (Q : Program) := 500+2*static Q+2*(callSize Q).size
def callFactor (Q : Program) := 4096+factor Q*(widthFactor Q+1)
def bits (x : List Bool) (base len e pc T : ℕ) := 1+x.length.size+base.size+len.size+e.size+pc.size+T.size

theorem allowance_bound (Q : Program) (x : List Bool) (base len e pc T : ℕ) :
    allowance Q x base len e pc T ≤ callFactor Q*(T+1)*bits x base len e pc T := by
  let U := bits x base len e pc T
  let B := widthFactor Q
  have pos : 1≤U := by dsimp [U,bits];omega
  have ep := size_add e 1
  change (e+1).size≤e.size+1+1 at ep
  have lab (a : ℕ) (h : a≤pc+callSize Q) : a.size ≤ pc.size+(callSize Q).size+1 :=
    (Nat.size_le_size h).trans (size_add ..)
  have l1 := lab (pc+setup.cmd.len+1+(tick Q).code.cmd.len+64) (by unfold callSize;omega)
  have l2 := lab (pc+setup.cmd.len+1+(body Q).len+1) (by unfold callSize;omega)
  have ws : runWidth Q x base len (e+1) (pc+setup.cmd.len) T ≤ B-4+4*U := by
    dsimp [B,widthFactor,U,bits,runWidth,overhead];omega
  have cb : 4 ≤ B := by dsimp [B,widthFactor];omega
  have wx : runWidth Q x base len (e+1) (pc+setup.cmd.len) T ≤ B*U := by
    have mul := Nat.mul_le_mul_left (B-4) pos
    have eq : B*U=(B-4)*U+4*U := by rw [←Nat.add_mul];congr 1;omega
    rw [eq];omega
  have init : 1024*(1+(e+1).size+e.size+x.length.size+base.size+len.size) ≤ 4096*U := by
    dsimp [U,bits];omega
  have TU : T ≤ (T+1)*U := (Nat.le_succ T).trans (Nat.le_mul_of_pos_right _ pos)
  have Ule : U≤(T+1)*U := Nat.le_mul_of_pos_left _ (by omega)
  have time := Nat.mul_le_mul_left (T+1) wx
  have all : (T+1)*runWidth Q x base len (e+1) (pc+setup.cmd.len) T+T ≤ (B+1)*((T+1)*U) := by
    calc
      _ ≤ (T+1)*(B*U)+(T+1)*U := Nat.add_le_add time TU
      _ = _ := by ring
  calc
    _ ≤ 4096*((T+1)*U)+factor Q*((B+1)*((T+1)*U)) := Nat.add_le_add (init.trans (Nat.mul_le_mul_left _ Ule)) (Nat.mul_le_mul_left _ all)
    _ = _ := by change _=(4096+factor Q*(B+1))*(T+1)*U;ring

/-- Public interface in terms of native instruction lists and observations of native registers. -/
theorem bounded_bit_subroutine (Q : Program) :
    ∃ (block : Cmd) (C : ℕ), ∀ (pre post : Program) (τ : Tapes) (st : State) (x : List Bool)
      (base len epoch T : ℕ) (v : Bool),
      Q.RunsIn (runTapes x (List.ofFn fun i : Fin len => τ.coins[base+i.val]?.getD false)) T (some [v]) →
      st.pc=pre.length → st.halted=false → st.bot=false → st.mem 0=0 → st.mem 10=epoch →
      (∀ i, st.mem (64+4*i) ≤ epoch) → (∀ i<x.length, st.mem (66+4*i)=bitVal x[i]?) →
      st.mem 67=T → st.mem 71=1 → st.mem 75=x.length → st.mem 79=base → st.mem 83=len →
      ∃ steps : ℕ, let P := pre++block.compile pre.length++post
        let u := (P.step τ)^[steps] st
        u.pc=pre.length+block.len ∧ u.halted=false ∧ u.bot=false ∧ u.out=st.out ∧
        u.mem 0=0 ∧ u.mem 10=epoch+1 ∧ (∀ i, u.mem (64+4*i)≤epoch+1) ∧ u.mem 22=v.toNat ∧
        (∀ i, u.mem (66+4*i)=st.mem (66+4*i)) ∧ (∀ i, i≠0 → u.mem (67+4*i)=st.mem (67+4*i)) ∧
        u.work ≤ st.work+C*(T+1)*(1+x.length.size+base.size+len.size+epoch.size+pre.length.size+T.size) := by
  refine ⟨call Q,callFactor Q,?_⟩
  intro pre post τ st x base len e T v time pc live normal zero clock valid input fuel one dim offset length
  let P := pre++(call Q).compile pre.length++post
  let s : Store := ⟨st.mem,st.out⟩
  have adm : Base s e := ⟨zero,clock,valid⟩
  have inp (i : ℕ) (hi : i<x.length) : s.mem (inputCell i)=bitVal x[i]? := by
    change st.mem (64+4*i+2)=_;rw [show 64+4*i+2=66+4*i by omega];exact input _ hi
  obtain ⟨u,t,steps,fee,path,loc,bas,frame,out,budget⟩ := call_runs Q P x base len e pre.length T τ s st v time
    ⟨pre,post,rfl,rfl⟩ ⟨pc,live,normal,rfl,rfl⟩ adm inp one fuel dim offset length
  have result := budget.trans (allowance_bound Q x base len e pre.length T)
  use steps
  change (let u := (P.step τ)^[steps] st; _) 
  dsimp only
  rw [path.1]
  refine ⟨loc.counter,loc.live,loc.normal,loc.output.trans frame.output,loc.memory ▸ bas.zero,
    loc.memory ▸ bas.clock,fun i => loc.memory ▸ bas.valid i,loc.memory ▸ out,?_,?_,?_⟩
  · intro i
    have eq : 66+4*i=inputCell i := by unfold inputCell tag;omega
    rw [eq,loc.memory];exact frame.input i
  · intro i hi
    have eq : 67+4*i=callerCell i := by unfold callerCell tag;omega
    rw [eq,loc.memory];exact frame.caller i hi
  · rw [path.2];exact Nat.add_le_add_left result _

end DirectedHamiltonicity.Main.CycleReduction.Guest

open TargetedSamplers TargetedSamplers.Structured

theorem solution (Q : Program) :
    ∃ (block : Cmd) (C : ℕ), ∀ (pre post : Program) (τ : Tapes) (st : State) (x : List Bool)
      (base len epoch T : ℕ) (v : Bool),
      Q.RunsIn ((⟨x,List.ofFn (fun i : Fin len => τ.coins[base+i.val]?.getD false),[],noOracle⟩ : Tapes)) T (some [v]) →
      st.pc=pre.length → st.halted=false → st.bot=false → st.mem 0=0 → st.mem 10=epoch →
      (∀ i, st.mem (64+4*i) ≤ epoch) → (∀ i<x.length, st.mem (66+4*i)=bitVal x[i]?) →
      st.mem 67=T → st.mem 71=1 → st.mem 75=x.length → st.mem 79=base → st.mem 83=len →
      ∃ steps : ℕ, let P := pre++block.compile pre.length++post
        let u := (P.step τ)^[steps] st
        u.pc=pre.length+block.len ∧ u.halted=false ∧ u.bot=false ∧ u.out=st.out ∧
        u.mem 0=0 ∧ u.mem 10=epoch+1 ∧ (∀ i, u.mem (64+4*i)≤epoch+1) ∧ u.mem 22=v.toNat ∧
        (∀ i, u.mem (66+4*i)=st.mem (66+4*i)) ∧ (∀ i, i≠0 → u.mem (67+4*i)=st.mem (67+4*i)) ∧
        u.work ≤ st.work+C*(T+1)*(1+x.length.size+base.size+len.size+epoch.size+pre.length.size+T.size) := by
  exact DirectedHamiltonicity.Main.CycleReduction.Guest.bounded_bit_subroutine Q
