-- Prove2me | solution 1 for TargetedSamplers.Structured.StackMachine.fields_call
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:43:27.001167+00:00
-- url     : https://prove2.me/submissions/7898548e-bbce-43ec-9204-b50eab72b638

import Definitions.Def_LogCostRAM_StructuredExecution
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option autoImplicit false

section StructuredLogCostRAM

/-! Structured, relocatable programs for the Prove2Me log-cost machine. All costs count
the primitive steps of the published instruction list, including jumps. -/

namespace TargetedSamplers.Structured

theorem Exec.post {τ inv c s t k} (e : Exec τ inv c s t k) (hs : inv s) : inv t := by
  induction e <;> solve_by_elim

/-- A live, ordinary machine state at the specified instruction, memory and output. -/
structure Located (st : State) (pc : ℕ) (s : Store) : Prop where
  counter : st.pc = pc
  live : st.halted = false
  normal : st.bot = false
  memory : st.mem = s.mem
  output : st.out = s.out

private theorem step_op {P : Program} (τ : Tapes) {st pc s} (h : Located st pc s)
    (p : Op) (hp : P[pc]? = some p.instruction) : Located (P.step τ st) (pc+1) (p.eval τ s) := by
  obtain ⟨hc,hh,hb,hm,ho⟩ := h
  cases p <;> constructor <;> simp_all [Op.instruction, Op.eval, Program.step, State.write, Store.write]

end TargetedSamplers.Structured

end StructuredLogCostRAM

section StructuredLogCostFragments

namespace TargetedSamplers.Structured

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

theorem dispatch_select {τ : Tapes} {inv : Store → Prop} (key scratch : ℕ) (hne : key ≠ scratch)
    (cs : List Cmd) (base : ℕ) (s t : Store) (j : Fin cs.length) (steps : ℕ)
    (tag : s.mem key = base+j.val) (safe : ∀ v ≤ base+j.val, inv (s.write scratch v))
    (branch : Exec τ inv cs[j.val] (s.write scratch (base+j.val)) t steps) :
    Exec τ inv (dispatch key scratch base cs) s t (3*j.val+2+steps) := by
  induction cs generalizing base s with
  | nil => exact Fin.elim0 j
  | cons c cs ih =>
    cases j using Fin.cases with
    | zero =>
      have h := safe base (by simp)
      have ht : (s.write scratch base).mem key ≤ (s.write scratch base).mem scratch := by
        simp [Store.write, hne, tag]
      have he : Exec τ inv c (s.write scratch base) t steps := by simpa using branch
      simpa [dispatch, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Exec.seq (Exec.op s (.const scratch base) h) (Exec.yes (n := dispatch key scratch (base+1) cs) ht he)
    | succ i =>
      let m := s.write scratch base
      have hm : inv m := safe _ (by simp)
      have hg : ¬m.mem key ≤ m.mem scratch := by
        simp [m, Store.write, hne, tag]
      have htag : m.mem key = base+1+i.val := by
        simpa [m, Store.write, Function.update_apply, hne, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tag
      have he := ih (base+1) m i htag (fun v hv => by
        simpa [m] using safe v (by simp at hv ⊢; omega)) (by
        simpa [m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using branch)
      have run := Exec.seq (Exec.op s (.const scratch base) hm) (Exec.no (y := c) hg he)
      convert run using 1 <;> simp [dispatch] <;> omega

end TargetedSamplers.Structured

end StructuredLogCostFragments

section LogCostRAMDivisionStep

namespace TargetedSamplers.Structured.Word

private theorem doublePair_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b z a : ℕ} {s : Store}
    (scale : s.mem (r 3) = z) (factor : s.mem (r 4) = a) (fit : s.Fits b)
    (hz : (2*z).size ≤ b) (hz' : (2*(2*z)).size ≤ b) (ha : (2*a).size ≤ b) :
    let t := ((doublePair r).run τ s).last
    Exec τ (fun u => u.Fits b) (doublePair r).cmd s t 3 ∧
      t.mem (r 3) = 2*z ∧ t.mem (r 4) = 2*a ∧ t.mem (r 5) = 2*(2*z) ∧ t.out = s.out ∧
      ∀ k, k ≠ r 3 → k ≠ r 4 → k ≠ r 5 → t.mem k = s.mem k := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  simp only [two_mul] at hz hz' ha
  have width : ((doublePair r).run τ s).writeWidth ≤ b := by
    simp [doublePair,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,scale,factor,hz,hz',ha]
  refine ⟨(doublePair r).exec τ s b fit width,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro k h3 h4 h5
       simp [doublePair,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
         Function.update_apply,h3,h4,h5])
    | simp [doublePair,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
        Function.update_apply,eq,scale,factor,two_mul]

/-- Select the largest shifted multiple fitting in the remainder. Only addition and a
comparison are used; doubling until the next multiple is too large takes 5j+1 primitive
instructions, where j is the selected shift. -/
theorem growPair_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b : ℕ} (j rem z a : ℕ) (s : Store)
    (scale : s.mem (r 3) = z) (factor : s.mem (r 4) = a) (dbl : s.mem (r 5) = 2*z)
    (upper : s.mem (r 6) = rem+1) (fit : s.Fits b) (width : (2*rem).size ≤ b)
    (amountWidth : (a*2^j).size ≤ b) (low : z*2^j ≤ rem) (high : rem < 2*(z*2^j)) :
    ∃ t, Exec τ (fun u => u.Fits b) (grow r) s t (5*j+1) ∧
      t.mem (r 3) = z*2^j ∧ t.mem (r 4) = a*2^j ∧ t.mem (r 5) = 2*(z*2^j) ∧ t.out = s.out ∧
      ∀ k, k ≠ r 3 → k ≠ r 4 → k ≠ r 5 → t.mem k = s.mem k := by
  induction j generalizing s z a with
  | zero =>
    simp only [pow_zero,Nat.mul_one] at high ⊢
    exact ⟨s,.done (by rw [upper,dbl]; omega),scale,factor,dbl,rfl,fun _ _ _ _ => rfl⟩
  | succ j ih =>
    have zs : 2*z*2^j = z*2^(j+1) := by rw [pow_succ]; ring
    have zs' : 2*z ≤ rem := (by
      have h := Nat.mul_le_mul_left (2*z) (Nat.one_le_two_pow (n := j))
      rw [Nat.mul_one,zs] at h
      exact h.trans low)
    have pw (v : ℕ) (hv : v ≤ 2*rem) : v.size ≤ b := (Nat.size_le_size hv).trans width
    have az : 2*a*2^j = a*2^(j+1) := by rw [pow_succ]; ring
    have amt : 2*a ≤ a*2^(j+1) := by
      simpa only [Nat.mul_one,az] using Nat.mul_le_mul_left (2*a) (Nat.one_le_two_pow (n := j))
    obtain ⟨ex,sz,sz',db,out,save⟩ := doublePair_exec (τ := τ) r scale factor fit
      (pw _ (by omega)) (pw _ (by omega)) ((Nat.size_le_size amt).trans amountWidth)
    let u := ((doublePair r).run τ s).last
    have ne {i k : Fin 9} (h : i ≠ k) := r.injective.ne h
    have up := (save (r 6) (ne (by decide)) (ne (by decide)) (ne (by decide))).trans upper
    obtain ⟨t,loop,finalZ,finalA,finalD,log,frame⟩ := ih (2*z) (2*a) u sz sz' db up
      (ex.post fit) (by rwa [az]) (by rwa [zs]) (by rwa [zs])
    have go : ¬s.mem (r 6) ≤ s.mem (r 5) := by rw [upper,dbl]; omega
    have count : 5*(j+1)+1 = 1+3+1+(5*j+1) := by omega
    refine ⟨t,?_,?_,?_,?_,log.trans out,?_⟩
    · rw [count]; exact .again go ex loop
    · simpa only [zs] using finalZ
    · simpa only [show 2*a*2^j = a*2^(j+1) by rw [pow_succ]; ring] using finalA
    · simpa only [zs] using finalD
    · intro k h3 h4 h5; exact (frame k h3 h4 h5).trans (save k h3 h4 h5)

/-- Specialization for division, where the quotient-place register never exceeds the
shifted divisor. -/
theorem grow_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b : ℕ} (j rem z a : ℕ) (s : Store)
    (scale : s.mem (r 3) = z) (factor : s.mem (r 4) = a) (dbl : s.mem (r 5) = 2*z)
    (upper : s.mem (r 6) = rem+1) (ha : a ≤ z) (fit : s.Fits b) (width : (2*rem).size ≤ b)
    (low : z*2^j ≤ rem) (high : rem < 2*(z*2^j)) :
    ∃ t, Exec τ (fun u => u.Fits b) (grow r) s t (5*j+1) ∧
      t.mem (r 3) = z*2^j ∧ t.mem (r 4) = a*2^j ∧ t.mem (r 5) = 2*(z*2^j) ∧ t.out = s.out ∧
      ∀ k, k ≠ r 3 → k ≠ r 4 → k ≠ r 5 → t.mem k = s.mem k := by
  have small := (Nat.mul_le_mul_right (2^j) ha).trans low
  exact growPair_exec r j rem z a s scale factor dbl upper fit width
    ((Nat.size_le_size (show a*2^j ≤ 2*rem by omega)).trans width) low high

/-- The binary shift is bounded by the number of bits of the dividend, independent of
the numerical quotient. -/
theorem shift_exists {d x : ℕ} (hd : 0 < d) (hx : d ≤ x) :
    ∃ j ≤ x.size, d*2^j ≤ x ∧ x < 2*(d*2^j) := by
  let q := x/d
  have hp : 0 < q := Nat.div_pos hx hd
  have pos := Nat.size_pos.mpr hp
  let j := q.size-1
  have hj : j+1 = q.size := by dsimp [j]; omega
  have hlo : 2^j ≤ q := Nat.lt_size.mp (by omega)
  have hhi : q < 2^(j+1) := by rw [hj]; exact Nat.lt_size_self q
  have small := (Nat.le_div_iff_mul_le hd).mp hlo
  have large := (Nat.div_lt_iff_lt_mul hd).mp hhi
  refine ⟨j,le_trans (by omega : j ≤ q.size) (Nat.size_le_size (Nat.div_le_self x d)),?_,?_⟩
  · simpa [Nat.mul_comm] using small
  · have e : 2^(j+1)*d = 2*(d*2^j) := by rw [pow_succ]; ring
    rwa [← e]

end TargetedSamplers.Structured.Word

end LogCostRAMDivisionStep

section LogCostRAMDivision

namespace TargetedSamplers.Structured.Word

structure DivRegs (r : Fin 9 ↪ ℕ) (s : Store) (rem d q : ℕ) : Prop where
  remReg : s.mem (r 0) = rem
  divisor : s.mem (r 1) = d
  quotient : s.mem (r 2) = q
  upper : s.mem (r 6) = rem+1
  zero : s.mem (r 7) = 0
  one : s.mem (r 8) = 1

theorem DivRegs.scratch {r : Fin 9 ↪ ℕ} {s t : Store} {rem d q : ℕ} (h : DivRegs r s rem d q)
    (frame : ∀ a, a ≠ r 3 → a ≠ r 4 → a ≠ r 5 → t.mem a = s.mem a) : DivRegs r t rem d q := by
  have get (i : Fin 9) (a : i ≠ 3) (b : i ≠ 4) (c : i ≠ 5) := frame (r i) (r.injective.ne a) (r.injective.ne b) (r.injective.ne c)
  exact ⟨(get 0 (by decide) (by decide) (by decide)).trans h.remReg,
    (get 1 (by decide) (by decide) (by decide)).trans h.divisor,(get 2 (by decide) (by decide) (by decide)).trans h.quotient,
    (get 6 (by decide) (by decide) (by decide)).trans h.upper,(get 7 (by decide) (by decide) (by decide)).trans h.zero,
    (get 8 (by decide) (by decide) (by decide)).trans h.one⟩

private theorem start_exec {r : Fin 9 ↪ ℕ} {τ : Tapes} {b rem d q : ℕ} {s : Store}
    (hr : DivRegs r s rem d q) (fit : s.Fits b) (hb : 1 ≤ b) (wd : (2*d).size ≤ b) :
    let t := ((startRound r).run τ s).last
    Exec τ (fun u => u.Fits b) (startRound r).cmd s t 3 ∧ t.mem (r 3) = d ∧ t.mem (r 4) = 1 ∧
      t.mem (r 5) = 2*d ∧ t.out = s.out ∧ ∀ a, a ≠ r 3 → a ≠ r 4 → a ≠ r 5 → t.mem a = s.mem a := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  have h := hr.divisor ▸ fit (r 1)
  have ww : ((startRound r).run τ s).writeWidth ≤ b := by
    simp only [two_mul] at wd
    simp [startRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,hr.divisor,hr.zero,wd,h,hb]
  refine ⟨(startRound r).exec τ s b fit ww,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro a n3 n4 n5; simp [startRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
        Function.update_apply,n3,n4,n5])
    | simp [startRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
        Function.update_apply,eq,hr.divisor,hr.zero,two_mul]

theorem finishRound_exec {r : Fin 9 ↪ ℕ} {τ : Tapes} {b rem d q z a : ℕ} {s : Store}
    (hr : DivRegs r s rem d q) (scale : s.mem (r 3) = z) (amount : s.mem (r 4) = a) (fit : s.Fits b)
    (wrem : (rem-z+1).size ≤ b) (wq : (q+a).size ≤ b) :
    let t := ((finishRound r).run τ s).last
    Exec τ (fun u => u.Fits b) (finishRound r).cmd s t 3 ∧ DivRegs r t (rem-z) d (q+a) ∧
      t.out = s.out ∧ ∀ k, (∀ i, k ≠ r i) → t.mem k = s.mem k := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  have ww' := (Nat.size_le_size (show rem-z ≤ rem-z+1 by omega)).trans wrem
  have ww : ((finishRound r).run τ s).writeWidth ≤ b := by
    simp [finishRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,hr.remReg,hr.quotient,hr.one,scale,amount,ww',wrem,wq]
  refine ⟨(finishRound r).exec τ s b fit ww,?_,rfl,?_⟩
  · constructor <;> simp [finishRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,eq,hr.remReg,hr.divisor,hr.quotient,hr.zero,hr.one,scale,amount]
  · intro k hk
    simp [finishRound,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,hk]

theorem size_lt_of_double_lt {old new : ℕ} (h : 2*new < old) : new.size < old.size := by
  have ho := Nat.size_pos.mpr (show 0 < old by omega)
  have e : 2^old.size = 2^(old.size-1)*2 := by
    conv_lhs => rw [show old.size = old.size-1+1 by omega,pow_succ]
  have lim := Nat.lt_size_self old
  rw [e] at lim
  have hn := Nat.size_le.mpr (show new < 2^(old.size-1) by omega)
  omega

/-- Quotient selection by maximal doubling removes at least half of the remainder at
each round. Thus division is polynomial in bit *length* on the addition-only RAM. -/
theorem quotientLoop_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {b : ℕ} (x d : ℕ) (hd : 0 < d)
    (hb : 1 ≤ b) (width : (2*x+2).size ≤ b) (fuel rem q : ℕ) (s : Store)
    (hr : DivRegs r s rem d q) (law : d*q+rem = x) (bound : rem.size ≤ fuel) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (quotientLoop r) s t j ∧ j ≤ fuel*(5*x.size+9)+1 ∧
      DivRegs r t (x%d) d (x/d) ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  have done {rem q fuel : ℕ} {s : Store} (hr : DivRegs r s rem d q) (law : d*q+rem = x) (lt : rem < d) :
      ∃ t j, Exec τ (fun u => u.Fits b) (quotientLoop r) s t j ∧ j ≤ fuel*(5*x.size+9)+1 ∧
        DivRegs r t (x%d) d (x/d) ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
    have eq : x = rem+d*q := by omega
    refine ⟨s,1,.done (by rw [hr.upper,hr.divisor]; omega),by omega,?_,rfl,fun _ _ => rfl⟩
    simpa only [eq,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lt,Nat.add_mul_div_left _ _ hd,
      Nat.div_eq_of_lt lt,Nat.zero_add] using hr
  induction fuel generalizing s rem q with
  | zero =>
    have h := Nat.size_eq_zero.mp (by omega : rem.size = 0)
    exact done hr law (by omega)
  | succ fuel ih =>
    by_cases stop : rem < d
    · exact done hr law stop
    have le : d ≤ rem := by omega
    obtain ⟨k,hk,low,high⟩ := shift_exists hd le
    have wr (v : ℕ) (hv : v ≤ 2*x+2) := (Nat.size_le_size hv).trans width
    obtain ⟨init,z,a,z₂,oi,fi⟩ := start_exec (τ := τ) hr fit hb (wr _ (by omega))
    obtain ⟨v,loop,scale,amount,_,og,fg⟩ := grow_exec (τ := τ) r k rem d 1 _ z a z₂
      (hr.scratch fi).upper hd (init.post fit) (wr _ (by omega)) low high
    let pow := 2^k
    let rem' := rem-d*pow
    have next : d*(q+pow)+rem' = x := by
      dsimp [rem',pow]; rw [Nat.mul_add]; omega
    have qx : q+pow ≤ x := by
      have h := Nat.mul_le_mul_right (q+pow) hd
      simp only [Nat.one_mul] at h; omega
    have red : 2*rem' < rem := by dsimp [rem',pow]; omega
    have shrink := size_lt_of_double_lt red
    obtain ⟨finish,hr',ofin,ff⟩ := finishRound_exec (τ := τ) ((hr.scratch fi).scratch fg) scale
      (show v.mem (r 4) = pow by simpa [pow] using amount) (loop.post (init.post fit))
      (wr _ (by change rem-d*pow+1 ≤ _; omega)) (wr _ (by omega))
    obtain ⟨t,j,rest,hj,reg,out,fre⟩ := ih rem' (q+pow) _ hr' next (by omega) (finish.post (loop.post (init.post fit)))
    have go : ¬s.mem (r 6) ≤ s.mem (r 1) := by rw [hr.upper,hr.divisor]; omega
    have hx := hk.trans (Nat.size_le_size (by omega : rem ≤ x))
    refine ⟨t,_,.again go (init.seq (loop.seq finish)) rest,?_,reg,out.trans (ofin.trans (og.trans oi)),?_⟩
    · rw [Nat.succ_mul fuel (5*x.size+9)]; omega
    · intro addr f
      exact (fre addr f).trans ((ff addr f).trans ((fg addr (f 3) (f 4) (f 5)).trans (fi addr (f 3) (f 4) (f 5))))

/-- Shared zero accumulator, constant registers, and upper bound for shifted arithmetic. -/
theorem initDiv_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {width : ℕ} (x d : ℕ) (s : Store)
    (input : s.mem (r 0) = x) (divisor : s.mem (r 1) = d) (fit : s.Fits width) (hb : 1 ≤ width)
    (upper : (x+1).size ≤ width) :
    let u := ((initDiv r).run τ s).last
    Exec τ (fun v => v.Fits width) (initDiv r).cmd s u 4 ∧ DivRegs r u x d 0 ∧ u.out = s.out ∧
      ∀ a, (∀ i, a ≠ r i) → u.mem a = s.mem a := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  let u := ((initDiv r).run τ s).last
  have good : ((initDiv r).run τ s).writeWidth ≤ width := by
    simp [initDiv,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
      Function.update_apply,eq,input,hb,upper]
  have init : Exec τ (fun v => v.Fits width) (initDiv r).cmd s u 4 := (initDiv r).exec τ s width fit good
  have hr : DivRegs r u x d 0 := by
    constructor <;> simp [u,initDiv,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,
      Function.update_apply,eq,input,divisor]
  have fr (a : ℕ) (f : ∀ i, a ≠ r i) : u.mem a = s.mem a := by
    simp [u,initDiv,TargetedSamplers.Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,f]
  exact ⟨init,hr,rfl,fr⟩

/-- Compute both natural division and remainder on the posted RAM, including divisor
zero. A b-bit dividend uses at most 5b²+9b+7 primitive instructions; the largest new
word is at most 2x+2. Caller memory is framed. -/
theorem divMod_exec (r : Fin 9 ↪ ℕ) {τ : Tapes} {width : ℕ} (x d : ℕ) (s : Store)
    (input : s.mem (r 0) = x) (divisor : s.mem (r 1) = d) (fit : s.Fits width)
    (hb : 1 ≤ width) (hw : (2*x+2).size ≤ width) :
    ∃ t j, Exec τ (fun u => u.Fits width) (divMod r) s t j ∧ j ≤ x.size*(5*x.size+9)+7 ∧
      t.mem (r 0) = x%d ∧ t.mem (r 2) = x/d ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  let u := ((initDiv r).run τ s).last
  obtain ⟨init,hr,_,fr⟩ := initDiv_exec (τ := τ) r x d s input divisor fit hb
    ((Nat.size_le_size (by omega : x+1 ≤ 2*x+2)).trans hw)
  by_cases hd : d = 0
  · refine ⟨u,_,init.seq (.yes (by rw [hr.divisor,hr.zero,hd]) (.skip u)),by omega,
      by simpa [hd] using hr.remReg,by simpa [hd] using hr.quotient,rfl,fr⟩
  · obtain ⟨t,j,loop,hj,out,ot,ft⟩ := quotientLoop_exec (τ := τ) r x d (by omega) hb hw x.size x 0 u hr
      (by simp) le_rfl (init.post fit)
    refine ⟨t,_,init.seq (.no (by rw [hr.divisor,hr.zero]; omega) loop),by omega,
      out.remReg,out.quotient,ot,fun a f => (ft a f).trans (fr a f)⟩

end TargetedSamplers.Structured.Word

end LogCostRAMDivision

section LogCostRAMMultiply

namespace TargetedSamplers.Structured.Word

private theorem startMultiple_exec {τ : TargetedSamplers.Tapes} (r : Fin 9 ↪ ℕ) {b rem y q : ℕ} {s : Store}
    (h : DivRegs r s rem y q) (fit : s.Fits b) (hb : 2 ≤ b) :
    let u := ((startMultiple r).run τ s).last
    Exec τ (fun t => t.Fits b) (startMultiple r).cmd s u 3 ∧ u.mem (r 3) = 1 ∧
      u.mem (r 4) = y ∧ u.mem (r 5) = 2 ∧ u.out = s.out ∧
      ∀ a, a ≠ r 3 → a ≠ r 4 → a ≠ r 5 → u.mem a = s.mem a := by
  have eq (i j : Fin 9) : r i = r j ↔ i=j := r.injective.eq_iff
  have hy := h.divisor ▸ fit (r 1)
  have two : (2:ℕ).size ≤ b := (by decide : (2:ℕ).size ≤ 2).trans hb
  have safe : ((startMultiple r).run τ s).writeWidth ≤ b := by
    simp [startMultiple,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,h.divisor,h.zero,hy,two]; omega
  refine ⟨(startMultiple r).exec τ s b fit safe,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro a h₃ h₄ h₅; simp [startMultiple,Structured.sequence,Fragment.run,Op.eval,Store.write,h₃,h₄,h₅])
    | simp [startMultiple,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,h.divisor,h.zero]

private theorem multiplyLoop_exec {τ : TargetedSamplers.Tapes} (r : Fin 9 ↪ ℕ) {b : ℕ} (x y : ℕ)
    (hb : 2 ≤ b) (wx : (2*x+2).size ≤ b) (wp : (x*y).size ≤ b) (fuel rem q : ℕ) (s : Store)
    (hr : DivRegs r s rem y q) (hx : rem ≤ x) (law : q+rem*y = x*y)
    (bound : rem.size ≤ fuel) (fit : s.Fits b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (multiplyLoop r) s t j ∧ j ≤ fuel*(5*x.size+9)+1 ∧
      t.mem (r 2) = x*y ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  have done {n q : ℕ} {s : Store} (hr : DivRegs r s 0 y q) (h : q+0*y = x*y) :
      ∃ t j, Exec τ (fun v => v.Fits b) (multiplyLoop r) s t j ∧ j ≤ n*(5*x.size+9)+1 ∧
        t.mem (r 2) = x*y ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a :=
    ⟨s,1,.done (by rw [hr.remReg,hr.zero]),by omega,hr.quotient.trans (by simpa using h),rfl,fun _ _ => rfl⟩
  induction fuel generalizing rem q s with
  | zero =>
    have zero : rem = 0 := Nat.size_eq_zero.mp (by omega)
    subst rem; exact done hr law
  | succ fuel ih =>
    by_cases hzero : rem=0
    · subst rem; exact done hr law
    obtain ⟨k,hk,lo,hi⟩ := shift_exists (by decide : 0 < 1) (show 1 ≤ rem by omega)
    simp only [Nat.one_mul] at lo hi
    let z := 2^k
    have amount : y*z ≤ x*y := by
      simpa only [Nat.mul_comm y z] using Nat.mul_le_mul_right y (lo.trans hx)
    obtain ⟨init,start,coeff,dbl,oi,fi⟩ := startMultiple_exec (τ := τ) r hr fit hb
    obtain ⟨u,loop,pow,term,_,og,fg⟩ := growPair_exec (τ := τ) r k rem 1 y _ start coeff dbl (hr.scratch fi).upper
      (init.post fit) ((Nat.size_le_size (by omega : 2*rem ≤ 2*x+2)).trans wx)
      ((Nat.size_le_size amount).trans wp) (by simpa using lo) (by simpa using hi)
    have split : z+(rem-z) = rem := Nat.add_sub_of_le lo
    have product := congrArg (fun v : ℕ => v*y) split
    simp only [Nat.add_mul] at product
    have law' : (q+y*z)+(rem-z)*y = x*y := by rw [Nat.mul_comm y z]; omega
    have sumWidth := (Nat.size_le_size (show q+y*z ≤ x*y by omega)).trans wp
    obtain ⟨finish,hnext,ofin,ff⟩ := finishRound_exec (τ := τ) ((hr.scratch fi).scratch fg)
      (show u.mem (r 3) = z by simpa only [Nat.one_mul] using pow) term (loop.post (init.post fit))
      ((Nat.size_le_size (by omega : rem-z+1 ≤ 2*x+2)).trans wx) sumWidth
    have shrink := size_lt_of_double_lt (show 2*(rem-z) < rem by change 2*(rem-2^k) < rem; omega)
    obtain ⟨t,j,tail,hj,answer,out,frame⟩ := ih (rem-z) (q+y*z) _ hnext (by omega) law' (by omega)
      (finish.post (loop.post (init.post fit)))
    have go : ¬s.mem (r 0) ≤ s.mem (r 7) := by rw [hr.remReg,hr.zero]; omega
    have cost := hk.trans (Nat.size_le_size hx)
    refine ⟨t,_,.again go (init.seq (loop.seq finish)) tail,?_,answer,out.trans (ofin.trans (og.trans oi)),?_⟩
    · rw [Nat.succ_mul fuel (5*x.size+9)]; omega
    · intro a free
      exact (frame a free).trans ((ff a free).trans ((fg a (free 3) (free 4) (free 5)).trans (fi a (free 3) (free 4) (free 5))))

/-- Multiply two arbitrary words on the addition-only logarithmic-cost RAM. Register 2
receives the exact product; the step count is quadratic in the bit length of the first
operand, including zero. No loop runs once per unit of an exponential operand. -/
theorem multiply_exec {τ : TargetedSamplers.Tapes} (r : Fin 9 ↪ ℕ) {b : ℕ} (x y : ℕ) (s : Store)
    (inX : s.mem (r 0) = x) (inY : s.mem (r 1) = y) (fit : s.Fits b) (hb : 2 ≤ b)
    (wx : (2*x+2).size ≤ b) (wp : (x*y).size ≤ b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (multiply r) s t j ∧ j ≤ x.size*(5*x.size+9)+5 ∧
      t.mem (r 2) = x*y ∧ t.out = s.out ∧ ∀ a, (∀ i, a ≠ r i) → t.mem a = s.mem a := by
  obtain ⟨init,regs,out,save⟩ := initDiv_exec (τ := τ) r x y s inX inY fit (by omega)
    ((Nat.size_le_size (by omega : x+1 ≤ 2*x+2)).trans wx)
  obtain ⟨t,j,loop,cost,correct,ret,frame⟩ := multiplyLoop_exec r x y hb wx wp x.size x 0 _ regs le_rfl
    (by simp) le_rfl (init.post fit)
  exact ⟨t,_,init.seq loop,by omega,correct,ret.trans out,fun a free => (frame a free).trans (save a free)⟩

end TargetedSamplers.Structured.Word

end LogCostRAMMultiply

section LogCostRAMPower

namespace TargetedSamplers.Structured.Word

private structure PowerState (r : Fin 13 ↪ ℕ) (s : Store) (x e a : ℕ) : Prop where
  base : s.mem (r 9) = x
  count : s.mem (r 10) = e
  result : s.mem (r 2) = a
  zero : s.mem (r 11) = 0
  one : s.mem (r 12) = 1

private theorem powerLoop_exec {τ : TargetedSamplers.Tapes} (r : Fin 13 ↪ ℕ) {b : ℕ} (x e a : ℕ)
    (s : Store) (h : PowerState r s x e a) (fit : s.Fits b) (hb : 2 ≤ b) (wx : (2*x+2).size ≤ b)
    (finalWidth : (a*x^e).size ≤ b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (powerLoop r) s t j ∧ j ≤ e*(x.size*(5*x.size+9)+10)+1 ∧
      t.mem (r 2) = a*x^e ∧ t.out = s.out ∧ ∀ v, (∀ i, v ≠ r i) → t.mem v = s.mem v := by
  have eq (i j : Fin 13) : r i = r j ↔ i=j := r.injective.eq_iff
  have ne {i j : Fin 13} (hne : i ≠ j) := r.injective.ne hne
  induction e generalizing s a with
  | zero =>
    exact ⟨s,1,.done (by rw [h.count,h.zero]),by simp,by simpa using h.result,rfl,fun _ _ => rfl⟩
  | succ e ih =>
    let u := ((powerOperands r).run τ s).last
    have xw := h.base ▸ fit (r 9)
    have aw := h.result ▸ fit (r 2)
    have safe : ((powerOperands r).run τ s).writeWidth ≤ b := by
      simp [powerOperands,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,eq,h.base,h.result,h.zero,xw,aw]
    have setup := (powerOperands r).exec τ s b fit safe
    have xarg : u.mem (r 0) = x := by simp [u,powerOperands,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,h.base,h.zero]
    have aarg : u.mem (r 1) = a := by simp [u,powerOperands,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,h.result,h.zero]
    have old (v : ℕ) (h₀ : v ≠ r 0) (h₁ : v ≠ r 1) : u.mem v = s.mem v := by
      simp [u,powerOperands,Structured.sequence,Fragment.run,Op.eval,Store.write,h₀,h₁]
    have step : x ≤ x^(e+1) := by
      by_cases z : x=0
      · simp [z]
      · simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < x) (by omega : 1 ≤ e+1)
    have part : x*a ≤ a*x^(e+1) := by simpa only [Nat.mul_comm x a] using Nat.mul_le_mul_left a step
    obtain ⟨v,k,mul,hk,product,out,fr⟩ := multiply_exec (τ := τ) (powerMulRegs r) x a u xarg aarg
      (setup.post fit) hb wx ((Nat.size_le_size part).trans finalWidth)
    have keep (i : Fin 13) (large : 9 ≤ i.val) : v.mem (r i) = s.mem (r i) := by
      have diff (j : Fin 13) (hj : j.val < 9) : i ≠ j := by intro he; subst j; omega
      have outside (j : Fin 9) : r i ≠ powerMulRegs r j := by
        intro he
        have same := congrArg (fun u : Fin 13 => u.val) (r.injective he)
        change i.val = j.val at same; have := j.isLt; omega
      exact (fr _ outside).trans (old _ (ne (diff 0 (by decide))) (ne (diff 1 (by decide))))
    let w := v.write (r 10) e
    have update : (Op.sub (r 10) (r 10) (r 12)).eval τ v = w := by
      simp [Op.eval,w,(keep 10 (by decide)).trans h.count,(keep 12 (by decide)).trans h.one]
    have countWidth : (e+1).size ≤ b := by rw [← h.count]; exact fit (r 10)
    have fw := Store.write_fits (mul.post (setup.post fit)) (r 10)
      ((Nat.size_le_size (Nat.le_succ e)).trans countWidth)
    have dec : Exec τ (fun v => v.Fits b) (.op (.sub (r 10) (r 10) (r 12))) v w 1 := by
      simpa only [update] using (Exec.op (τ := τ) (inv := fun v => v.Fits b) v (.sub (r 10) (r 10) (r 12)) (by rwa [update]))
    change v.mem (r 2) = x*a at product
    have next : PowerState r w x e (x*a) := by
      constructor <;> simp [w,Store.write,eq,keep 9 (by decide),keep 11 (by decide),keep 12 (by decide),
        h.base,h.zero,h.one,product]
    have total : x*a*x^e = a*x^(e+1) := by rw [pow_succ]; ring
    obtain ⟨t,j,loop,hj,last,ret,save⟩ := ih (x*a) w next fw (by rwa [total])
    have go : ¬s.mem (r 10) ≤ s.mem (r 11) := by rw [h.count,h.zero]; omega
    have setupSteps : ((powerOperands r).run τ s).steps = 2 := rfl
    refine ⟨t,_,.again go (setup.seq (mul.seq dec)) loop,?_,last.trans total,ret.trans out,?_⟩
    · rw [Nat.succ_mul e (x.size*(5*x.size+9)+10)]; omega
    · intro v' free
      have outside (j : Fin 9) : v' ≠ powerMulRegs r j := free ⟨j.val,by have := j.isLt; omega⟩
      exact (save _ free).trans ((show w.mem v' = v.mem v' by simp [w,Store.write,free]).trans
        ((fr v' outside).trans (old _ (free 0) (free 1))))

/-- Raise a word to an input exponent by counted multiplication. The loop count is the
exponent itself, and each iteration costs a polynomial in the base's bit length. -/
theorem power_exec {τ : TargetedSamplers.Tapes} (r : Fin 13 ↪ ℕ) {b : ℕ} (x e : ℕ) (s : Store)
    (base : s.mem (r 9) = x) (exponent : s.mem (r 10) = e) (fit : s.Fits b) (hb : 2 ≤ b)
    (wx : (2*x+2).size ≤ b) (wp : (x^e).size ≤ b) :
    ∃ t j, Exec τ (fun v => v.Fits b) (power r) s t j ∧ j ≤ e*(x.size*(5*x.size+9)+10)+4 ∧
      t.mem (r 2) = x^e ∧ t.out = s.out ∧ ∀ v, (∀ i, v ≠ r i) → t.mem v = s.mem v := by
  have eq (i j : Fin 13) : r i = r j ↔ i=j := r.injective.eq_iff
  let u := ((initPower r).run τ s).last
  have safe : ((initPower r).run τ s).writeWidth ≤ b := by
    simp [initPower,Structured.sequence,Fragment.run,Op.written]; omega
  have init := (initPower r).exec τ s b fit safe
  have regs : PowerState r u x e 1 := by
    constructor <;> simp [u,initPower,Structured.sequence,Fragment.run,Op.eval,Store.write,eq,base,exponent]
  obtain ⟨t,j,loop,hj,last,ret,fr⟩ := powerLoop_exec (τ := τ) r x e 1 u regs (init.post fit) hb wx (by simpa using wp)
  have count : ((initPower r).run τ s).steps = 3 := rfl
  refine ⟨t,_,init.seq loop,by omega,by simpa using last,ret,?_⟩
  intro v free
  simpa [u,initPower,Structured.sequence,Fragment.run,Op.eval,Store.write,free] using fr v free

end TargetedSamplers.Structured.Word

end LogCostRAMPower

section LogCostRAMArithmetic

namespace TargetedSamplers.Structured.Word

theorem size_twice_add_two (x : ℕ) : (2*x+2).size ≤ x.size+2 := by
  apply Nat.size_le.mpr
  have scale : 2^(x.size+2) = 4*2^x.size := by rw [pow_add]; ring
  rw [scale]
  have := Nat.lt_size_self x; omega

def Arithmetic.steps : Arithmetic → ℕ → ℕ → ℕ
  | .mul, x, _ => x.size*(5*x.size+9)+5
  | .div, x, _ | .mod, x, _ => x.size*(5*x.size+9)+7
  | .pow, x, y => y*(x.size*(5*x.size+9)+10)+4

private theorem Arithmetic.native_exec {τ : TargetedSamplers.Tapes} (op : Arithmetic) {b : ℕ}
    (x y : ℕ) (s : Store) (left : s.mem op.leftReg = x) (right : s.mem op.rightReg = y)
    (fit : s.Fits b) (hb : 2 ≤ b) (wx : (2*x+2).size ≤ b) (wy : (op.value x y).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) op.native s t j ∧ j ≤ op.steps x y ∧
      t.mem op.outReg = op.value x y ∧ t.out = s.out ∧ ∀ a, 13 ≤ a → t.mem a = s.mem a := by
  have outside (n : ℕ) (hn : n ≤ 13) (a : ℕ) (ha : 13 ≤ a) (i : Fin n) : a ≠ Fin.valEmbedding i := by
    change a ≠ i.val; have := i.isLt; omega
  cases op with
  | mul =>
    obtain ⟨t,j,ex,hj,ans,out,fr⟩ := multiply_exec (τ := τ) Fin.valEmbedding x y s left right fit hb wx wy
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 9 (by decide) a ha)⟩
  | div =>
    obtain ⟨t,j,ex,hj,_,ans,out,fr⟩ := divMod_exec (τ := τ) Fin.valEmbedding x y s left right fit (by omega) wx
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 9 (by decide) a ha)⟩
  | mod =>
    obtain ⟨t,j,ex,hj,ans,_,out,fr⟩ := divMod_exec (τ := τ) Fin.valEmbedding x y s left right fit (by omega) wx
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 9 (by decide) a ha)⟩
  | pow =>
    obtain ⟨t,j,ex,hj,ans,out,fr⟩ := power_exec (τ := τ) Fin.valEmbedding x y s left right fit hb wx wy
    exact ⟨t,j,ex,hj,ans,out,fun a ha => fr a (outside 13 le_rfl a ha)⟩

private theorem loadArgs_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (p q l r : ℕ) (s : Store)
    (hp : p < 13) (hq : q < 13) (ne : p ≠ q) (fit : s.Fits b) :
    let t := ((loadArgs p q l r).run τ s).last
    Exec τ (fun u => u.Fits b) (loadArgs p q l r).cmd s t 3 ∧ t.mem p = s.mem (cell l) ∧
      t.mem q = s.mem (cell r) ∧ t.mem 13 = 0 ∧ t.out = s.out ∧ ∀ i, t.mem (cell i) = s.mem (cell i) := by
  have far (i v : ℕ) (h : v ≤ 13) : cell i ≠ v := by dsimp [cell]; omega
  have z : 13 ≠ p := by omega
  have safe : ((loadArgs p q l r).run τ s).writeWidth ≤ b := by
    simp [loadArgs,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,far l 13 le_rfl,far r 13 le_rfl,
      far r p hp.le,z,fit (cell l),fit (cell r)]
  refine ⟨(loadArgs p q l r).exec τ s b fit safe,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (intro i; simp [loadArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,far i p hp.le,far i q hq.le,far i 13 le_rfl])
    | simp [loadArgs,Structured.sequence,Fragment.run,Op.eval,Store.write,ne,far l 13 le_rfl,far r 13 le_rfl,
        far r p hp.le,z,show 13 ≠ q by omega]

theorem Arithmetic.call_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (op : Arithmetic) (d l r : ℕ) (s : Store)
    (fit : s.Fits b) (hb : 2 ≤ b) :
    let x := s.mem (cell l)
    let y := s.mem (cell r)
    (2*x+2).size ≤ b → (op.value x y).size ≤ b →
    ∃ t j, Exec τ (fun u => u.Fits b) (op.call d l r) s t j ∧ j ≤ op.steps x y+4 ∧ t.out = s.out ∧
      ∀ i, t.mem (cell i) = if i=d then op.value x y else s.mem (cell i) := by
  intro x y wx wy
  obtain ⟨load,left,right,zero,out₀,fr₀⟩ := loadArgs_exec (τ := τ) op.leftReg op.rightReg l r s
    (by cases op <;> decide) (by cases op <;> decide) (by cases op <;> decide) fit
  obtain ⟨v,j,run,hj,value,out,fr⟩ := op.native_exec (τ := τ) x y _ left right (load.post fit) hb wx wy
  let t := v.write (cell d) (op.value x y)
  have put : (Op.add (cell d) op.outReg 13).eval τ v = t := by simp [Op.eval,t,value,(fr 13 le_rfl).trans zero]
  have write : Exec τ (fun u => u.Fits b) (.op (.add (cell d) op.outReg 13)) v t 1 := by
    simpa only [put] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) v (.add (cell d) op.outReg 13)
      (by rw [put]; exact Store.write_fits (run.post (load.post fit)) _ wy))
  refine ⟨t,_,load.seq (run.seq write),by omega,out.trans out₀,?_⟩
  intro i
  by_cases eq : i=d
  · subst i; simp [t,Store.write]
  · have ne : cell i ≠ cell d := by simpa [cell] using eq
    simp [t,Store.write,ne,eq,(fr (cell i) (by dsimp [cell]; omega)).trans (fr₀ i)]

end TargetedSamplers.Structured.Word

end LogCostRAMArithmetic

section LogCostRAMArithmeticCircuit

namespace TargetedSamplers.Structured.Word

def Expression.steps (v : ℕ → ℕ) : Expression → ℕ
  | .arithmetic op l r => op.steps (v l) (v r)+4
  | _ => 1

def Expression.width (v : ℕ → ℕ) (e : Expression) : ℕ :=
  match e with
  | .arithmetic _ l _ => max (2*v l+2).size (e.eval v).size
  | _ => (e.eval v).size

/-- The only arithmetic loop counted in the numerical value of an operand is a power's
exponent. The other primitives have cost polynomial in word width. -/
def Expression.multiplicity (v : ℕ → ℕ) : Expression → ℕ
  | .arithmetic .pow _ r => v r+1
  | _ => 1

theorem Expression.steps_le (e : Expression) (v : ℕ → ℕ) (b : ℕ) (h : e.width v ≤ b) :
    e.steps v ≤ e.multiplicity v*(b*(5*b+9)+15) := by
  cases e with
  | literal | add | sub => simp [steps,multiplicity]
  | arithmetic op l r =>
    have wl := (max_le_iff.mp h).1
    have le := (Nat.size_le_size (show v l ≤ 2*v l+2 by omega)).trans wl
    have quad := Nat.mul_le_mul le (show 5*(v l).size+9 ≤ 5*b+9 by omega)
    cases op with
    | mul | div | mod => simp [steps,multiplicity,Arithmetic.steps]; omega
    | pow =>
      simp only [steps,multiplicity,Arithmetic.steps,Nat.succ_mul (v r) (b*(5*b+9)+15)]
      have := Nat.mul_le_mul_left (v r) (show (v l).size*(5*(v l).size+9)+10 ≤ b*(5*b+9)+15 by omega)
      omega

def Assignment.update (a : Assignment) (v : ℕ → ℕ) := Function.update v a.dst (a.rhs.eval v)

def Represents (s : Store) (v : ℕ → ℕ) : Prop := ∀ i, s.mem (cell i) = v i

theorem Assignment.exec {τ : TargetedSamplers.Tapes} {b : ℕ} (a : Assignment) (v : ℕ → ℕ) (s : Store)
    (h : Represents s v) (fit : s.Fits b) (hb : 2 ≤ b) (width : a.rhs.width v ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) a.cmd s t j ∧ j ≤ a.rhs.steps v ∧ Represents t (a.update v) ∧ t.out = s.out := by
  obtain ⟨d,e⟩ := a
  have simple (op : Op) (z : ℕ) (ev : op.eval τ s = s.write (cell d) z) (wz : z.size ≤ b) :
      let t := s.write (cell d) z
      Exec τ (fun u => u.Fits b) (.op op) s t 1 ∧ Represents t (Function.update v d z) ∧ t.out = s.out := by
    refine ⟨?_,?_,rfl⟩
    · simpa only [ev] using (Exec.op (τ := τ) (inv := fun u => u.Fits b) s op (by rw [ev]; exact Store.write_fits fit _ wz))
    · intro i
      by_cases eq : i=d
      · subst i; simp [Store.write]
      · have dif : cell i ≠ cell d := by simpa [cell] using eq
        simpa [Store.write,Function.update_of_ne eq,Function.update_of_ne dif] using h i
  cases e with
  | literal x =>
    obtain ⟨ex,post,out⟩ := simple (.const (cell d) x) x rfl width
    exact ⟨_,1,ex,le_rfl,post,out⟩
  | add l r =>
    obtain ⟨ex,post,out⟩ := simple (.add (cell d) (cell l) (cell r)) (v l+v r) (by simp [Op.eval,h l,h r]) width
    exact ⟨_,1,ex,le_rfl,post,out⟩
  | sub l r =>
    obtain ⟨ex,post,out⟩ := simple (.sub (cell d) (cell l) (cell r)) (v l-v r) (by simp [Op.eval,h l,h r]) width
    exact ⟨_,1,ex,le_rfl,post,out⟩
  | arithmetic op l r =>
    change max (2*v l+2).size (op.value (v l) (v r)).size ≤ b at width
    obtain ⟨wl,wr⟩ := max_le_iff.mp width
    obtain ⟨t,j,ex,work,out,regs⟩ := op.call_exec (τ := τ) d l r s fit hb (by rwa [h l]) (by rwa [h l,h r])
    refine ⟨t,j,ex,by simpa only [Expression.steps,h l,h r] using work,?_,out⟩
    intro i
    by_cases eq : i=d
    · subst i; simpa [Assignment.update,Expression.eval,h l,h r] using regs d
    · simpa [Assignment.update,Expression.eval,Function.update_of_ne eq,eq,h i] using regs i

namespace Circuit

def result (v : ℕ → ℕ) : List Assignment → (ℕ → ℕ)
  | [] => v
  | a::as => result (a.update v) as

def steps (v : ℕ → ℕ) : List Assignment → ℕ
  | [] => 0
  | a::as => a.rhs.steps v + steps (a.update v) as

def width (v : ℕ → ℕ) : List Assignment → ℕ
  | [] => 0
  | a::as => max (a.rhs.width v) (width (a.update v) as)

def multiplicity (v : ℕ → ℕ) : List Assignment → ℕ
  | [] => 0
  | a::as => a.rhs.multiplicity v + multiplicity (a.update v) as

theorem steps_le (as : List Assignment) (v : ℕ → ℕ) (b : ℕ) (h : width v as ≤ b) :
    steps v as ≤ multiplicity v as*(b*(5*b+9)+15) := by
  induction as generalizing v with
  | nil => simp [steps,multiplicity]
  | cons a as ih =>
    obtain ⟨first,rest⟩ := max_le_iff.mp h
    simpa only [steps,multiplicity,Nat.add_mul] using Nat.add_le_add (a.rhs.steps_le v b first) (ih (a.update v) rest)

theorem result_untouched (as : List Assignment) (v : ℕ → ℕ) (i : ℕ) (free : ∀ a ∈ as, i ≠ a.dst) :
    result v as i = v i := by
  induction as generalizing v with
  | nil => rfl
  | cons a as ih =>
    rw [result,ih (a.update v) (fun x hx => free x (List.mem_cons_of_mem _ hx))]
    exact Function.update_of_ne (free a (by simp)) _ _

/-- A finite arithmetic circuit is a fixed program on the public RAM. Its bound is a
sum of the individual operation costs, and its width accounts for their intermediates. -/
theorem exec {τ : TargetedSamplers.Tapes} {b : ℕ} (as : List Assignment) (v : ℕ → ℕ) (s : Store)
    (repr : Represents s v) (fit : s.Fits b) (hb : 2 ≤ b) (bound : width v as ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (cmd as) s t j ∧ j ≤ steps v as ∧ Represents t (result v as) ∧ t.out = s.out := by
  induction as generalizing v s with
  | nil => exact ⟨s,0,.skip s,le_rfl,repr,rfl⟩
  | cons a as ih =>
    obtain ⟨first,later⟩ := max_le_iff.mp bound
    obtain ⟨u,i,run,hi,rep,out⟩ := a.exec (τ := τ) v s repr fit hb first
    obtain ⟨t,j,tail,hj,final,ret⟩ := ih (a.update v) u rep (run.post fit) later
    exact ⟨t,_,run.seq tail,Nat.add_le_add hi hj,final,ret.trans out⟩

end Circuit

end TargetedSamplers.Structured.Word

end LogCostRAMArithmeticCircuit

section PackedBinaryStacks

namespace TargetedSamplers.Structured.BinaryStack

open Word

@[simp] theorem packed_nil : packed [] = 1 := rfl

theorem packed_cons (b : Bool) (xs : List Bool) : packed (b::xs) = packed xs+packed xs+b.toNat := by
  cases b <;> simp [packed,Nat.bit,two_mul]

theorem packed_pos (xs : List Bool) : 0 < packed xs := by
  induction xs with
  | nil => decide
  | cons b xs ih => rw [packed_cons]; omega

@[simp] theorem packed_size (xs : List Bool) : (packed xs).size = xs.length+1 := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    change (Nat.bit b (packed xs)).size = _
    rw [Nat.size_bit (Nat.ne_of_gt (packed_pos (b::xs))),ih,List.length_cons]

def headSymbol : List Bool → ℕ
  | [] => 0
  | b::_ => 1+b.toNat

def headOfWord (x : ℕ) := if x ≤ 1 then 0 else x-(x/2+x/2)+1

theorem headOfWord_packed (xs : List Bool) : headOfWord (packed xs) = headSymbol xs := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    have pos := packed_pos xs
    rw [headOfWord,packed_cons,if_neg (show ¬ packed xs+packed xs+b.toNat ≤ 1 by omega)]
    cases b <;> simp only [headSymbol,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem tail_of_packed {xs : List Bool} (nonempty : xs ≠ []) : packed xs / 2 = packed xs.tail := by
  cases xs with
  | nil => contradiction
  | cons b xs => cases b <;> simp [packed_cons] <;> omega

/-- The three fixed constants used by the stack and finite-control instructions. -/
structure Constants (s : Store) : Prop where
  one : s.mem (cell 1) = 1
  two : s.mem (cell 2) = 2
  zero : s.mem (cell 5) = 0

theorem push_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (k : ℕ) (hk : 8 ≤ k) (bit : Bool)
    (xs : List Bool) (s : Store) (c : Constants s) (v : s.mem (cell k) = packed xs) (fit : s.Fits b)
    (room : xs.length+2 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (push k bit) s t j ∧ j ≤ 2 ∧
      t.mem (cell k) = packed (bit::xs) ∧ t.out = s.out ∧ ∀ a, a ≠ cell k → t.mem a = s.mem a := by
  let x := packed xs
  let u := s.write (cell k) (x+x)
  have ev : (Op.add (cell k) (cell k) (cell k)).eval τ s = u := by simp [Op.eval,u,x,v]
  have size : (x+x).size ≤ b := by
    have e : x+x = packed (false::xs) := by simp [packed_cons,x]
    rw [e,packed_size,List.length_cons]; omega
  have fu := Store.write_fits fit (cell k) size
  have first : Exec τ (fun st => st.Fits b) (.op (.add (cell k) (cell k) (cell k))) s u 1 := by
    simpa only [ev] using (Exec.op (τ := τ) (inv := fun st => st.Fits b) s (.add (cell k) (cell k) (cell k)) (by rw [ev]; exact fu))
  cases bit with
  | false => exact ⟨u,1,first,by decide,by simp [u,Store.write,packed_cons,x],rfl,fun a h => by simp [u,Store.write,h]⟩
  | true =>
    have diff : cell 1 ≠ cell k := by simp [cell]; omega
    have e : (Op.add (cell k) (cell k) (cell 1)).eval τ u = u.write (cell k) (packed (true::xs)) := by
      simp [Op.eval,u,Store.write,diff,c.one,packed_cons,x]
    have second := Exec.op (τ := τ) (inv := fun st => st.Fits b) u (.add (cell k) (cell k) (cell 1))
      (by rw [e]; exact Store.write_fits fu _ (by rw [packed_size,List.length_cons]; omega))
    exact ⟨_,2,first.seq second,le_rfl,by rw [e]; simp [Store.write],rfl,
      fun a h => by rw [e]; simp [u,Store.write,h]⟩

private def cut (k : ℕ) (remove : Bool) : List Assignment :=
  [⟨4,.arithmetic .div k 2⟩,⟨3,.add 4 4⟩,⟨6,.sub k 3⟩,⟨6,.add 6 1⟩] ++
    (if remove then [⟨k,.add 4 5⟩] else [])

def inspect (k : ℕ) (remove : Bool) : Cmd := .branch (cell k) (cell 1)
  (.op (.const (cell 6) 0)) (Circuit.cmd (cut k remove))

/-- Inspect a stack's top symbol and optionally pop it. Arbitrarily long stacks use
binary division on an explicitly bounded word, with no unit-cost division instruction. -/
theorem inspect_exec {τ : TargetedSamplers.Tapes} {b : ℕ} (k : ℕ) (hk : 8 ≤ k) (remove : Bool)
    (xs : List Bool) (s : Store) (c : Constants s) (v : s.mem (cell k) = packed xs) (fit : s.Fits b)
    (room : xs.length+3 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (inspect k remove) s t j ∧ j ≤ 5*(b*(5*b+9)+15)+2 ∧
      t.mem (cell 6) = headSymbol xs ∧ t.mem (cell k) = packed (if remove then xs.tail else xs) ∧ t.out = s.out ∧
      ∀ i, i ≠ k → i ≠ 3 → i ≠ 4 → i ≠ 6 → t.mem (cell i) = s.mem (cell i) := by
  by_cases nil : xs = []
  · subst xs
    have ex := Exec.op (τ := τ) (inv := fun st => st.Fits b) s (.const (cell 6) 0) (Store.write_fits fit _ (by simp))
    refine ⟨_,_,Exec.yes (n := Circuit.cmd (cut k remove)) (by rw [v,c.one]; decide) ex,by omega,?_,?_,rfl,?_⟩
    · simp [Op.eval,Store.write,headSymbol]
    · have diff : cell k ≠ cell 6 := by simp [cell]; omega
      cases remove <;> simp [Op.eval,Store.write,diff,v]
    · intro i _ _ _ hi
      have neq : cell i ≠ cell 6 := by dsimp [cell]; omega
      simp [Op.eval,Store.write,neq]
  · let vals := fun i => s.mem (cell i)
    let x := packed xs
    have vx : vals k = x := v
    have c₁ : vals 1 = 1 := c.one
    have c₂ : vals 2 = 2 := c.two
    have c₅ : vals 5 = 0 := c.zero
    have notSmall : 1 < x := by
      cases xs with
      | nil => contradiction
      | cons bit bs =>
        change 1 < packed (bit::bs)
        rw [packed_cons]; have := packed_pos bs; omega
    have dif (i : ℕ) (hi : i < 8) : k ≠ i := by omega
    have rev (i : ℕ) (hi : i < 8) : i ≠ k := by omega
    have wx : x.size+2 ≤ b := by simpa [x] using room
    have xx := (size_twice_add_two x).trans wx
    have half : (x/2).size ≤ b := (Nat.size_le_size (Nat.div_le_self _ _)).trans (by omega)
    have twice : (x/2+x/2).size ≤ b := (Nat.size_le_size (show x/2+x/2 ≤ x by omega)).trans (by omega)
    have rem : (x-(x/2+x/2)).size ≤ b := (Nat.size_le_size (Nat.sub_le _ _)).trans (by omega)
    have out : (x-(x/2+x/2)+1).size ≤ b := (Nat.size_le_size (show x-(x/2+x/2)+1 ≤ 2 by omega)).trans
      (show (2:ℕ).size ≤ b by change 2 ≤ b; omega)
    have width : Circuit.width vals (cut k remove) ≤ b := by
      cases remove <;> simp (disch := decide) [cut,Circuit.width,Assignment.update,Expression.width,Expression.eval,
        Arithmetic.value,Function.update_apply,dif,rev,vx,c₁,c₂,c₅,xx,half,twice,rem,out]
    obtain ⟨t,j,run,work,regs,hout⟩ := Circuit.exec (τ := τ) (cut k remove) vals s (fun _ => rfl) fit (by omega) width
    have wt := Circuit.steps_le (cut k remove) vals b width
    have count : Circuit.multiplicity vals (cut k remove) ≤ 5 := by
      cases remove <;> norm_num [cut,Circuit.multiplicity,Expression.multiplicity]
    have time := Nat.mul_le_mul_right (b*(5*b+9)+15) count
    have output : Circuit.result vals (cut k remove) 6 = headOfWord x := by
      cases remove <;> simp (disch := decide) [cut,Circuit.result,Assignment.update,Expression.eval,Arithmetic.value,Function.update_apply,
        dif,rev,vx,c₁,c₂,c₅,headOfWord,show ¬x ≤ 1 by omega]
    have stack : Circuit.result vals (cut k remove) k = (if remove then x/2 else x) := by
      cases remove <;> simp (disch := decide) [cut,Circuit.result,Assignment.update,Expression.eval,Arithmetic.value,Function.update_apply,
        dif,rev,vx,c₁,c₂,c₅]
    have unchanged (i : ℕ) (hi : i ≠ k) (h₃ : i ≠ 3) (h₄ : i ≠ 4) (h₆ : i ≠ 6) :
        t.mem (cell i) = s.mem (cell i) := by
      apply (regs i).trans
      apply Circuit.result_untouched
      cases remove <;> simp [cut,hi,h₃,h₄,h₆]
    refine ⟨t,_,Exec.no (y := .op (.const (cell 6) 0)) (by rw [v,c.one]; exact Nat.not_le_of_gt notSmall) run,
      by omega,(regs 6).trans (output.trans (headOfWord_packed xs)),?_,hout,unchanged⟩
    rw [regs k,stack]; cases remove <;> simp [x,tail_of_packed nil]

end TargetedSamplers.Structured.BinaryStack

end PackedBinaryStacks

section PackedBitWriter

namespace TargetedSamplers.Structured.BinaryStack

open Word

/-- Packing the native little-endian binary natural adds its single high sentinel. -/
theorem packed_nat_bits (n : ℕ) : packed n.bits = n+2^n.size := by
  induction n using Nat.binaryRec with
  | zero => rfl
  | bit bit n ih =>
    by_cases hn : n=0
    · subst n; cases bit <;> rfl
    · have nonzero : Nat.bit bit n ≠ 0 := by cases bit <;> simp [Nat.bit] <;> omega
      rw [Nat.bits_append_bit _ _ (fun h => (hn h).elim),packed_cons,ih,Nat.size_bit nonzero,pow_succ]
      cases bit <;> simp [Nat.bit] <;> omega

end TargetedSamplers.Structured.BinaryStack

end PackedBitWriter

section NativeNumericFields

namespace TargetedSamplers.NumericFields

def read (radix : ℕ) : ℕ → ℕ → ℕ
  | 0,x => x%radix
  | i+1,x => read radix i (x/radix)

theorem read_join (radix : ℕ) (positive : 0 < radix) (xs : List ℕ) (bound : ∀ a∈xs,a < radix)
    (top i : ℕ) (hi : i < xs.length) : read radix i (join radix xs top)=xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have small := bound x (by simp)
    cases i with
    | zero => simp [read,join,Nat.mod_eq_of_lt small]
    | succ i =>
      rw [read,join,Nat.add_mul_div_left _ _ positive,Nat.div_eq_of_lt small,Nat.zero_add]
      exact ih (fun a ha => bound a (by simp [ha])) i (by simpa using hi)

theorem bounds (w : ℕ) (xs : List ℕ) (h : ∀ x∈xs,x < 2^w) :
    2^(w*xs.length) ≤ pack w xs ∧ pack w xs < 2^(w*xs.length+1) := by
  induction xs with
  | nil => simp [pack,join]
  | cons x xs ih =>
    have digit := h x (by simp)
    obtain ⟨low,high⟩ := ih (fun a ha => h a (by simp [ha]))
    have pos := Nat.two_pow_pos w
    have scaled := Nat.mul_le_mul_left (2^w) low
    have scaledTop := Nat.mul_le_mul_left (2^w) (Nat.succ_le_of_lt high)
    change _ ≤ x+2^w*pack w xs ∧ x+2^w*pack w xs < _
    rw [List.length_cons,Nat.mul_succ,Nat.add_comm (w*xs.length) w, pow_add,
      Nat.add_assoc w (w*xs.length) 1,pow_add]
    rw [Nat.mul_succ] at scaledTop
    omega

theorem pack_size (w : ℕ) (xs : List ℕ) (h : ∀ x∈xs,x < 2^w) : (pack w xs).size=w*xs.length+1 := by
  obtain ⟨lo,hi⟩ := bounds w xs h
  apply Nat.le_antisymm (Nat.size_le.mpr hi)
  by_contra! small
  have up := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : (pack w xs).size ≤ w*xs.length)
  have pos := Nat.lt_size_self (pack w xs)
  omega

/-- The same straight-line accumulation also constructs the packed input stack:
starting at three installs both the request sentinel and the native stack sentinel. -/
theorem native_packed (w : ℕ) (xs : List ℕ) :
    join (2^w) xs 3=pack w xs+2^(w*xs.length+1) := by
  induction xs with
  | nil => simp [pack,join]
  | cons x xs ih =>
    change x+2^w*join (2^w) xs 3 = x+2^w*pack w xs+2^(w*(x::xs).length+1)
    rw [ih,List.length_cons,Nat.mul_succ]
    rw [show w*xs.length+w+1=w+(w*xs.length+1) by omega,pow_add]
    simp only [pow_add,Nat.mul_add,Nat.add_assoc]

end TargetedSamplers.NumericFields

end NativeNumericFields

section TM2RAMStacks

namespace TargetedSamplers.Structured.StackMachine

open Word BinaryStack Turing

structure Layout (K Λ σ : Type) where
  tapes : ℕ
  tags : ℕ
  tape : K ≃ Fin tapes
  control : (Λ × σ) ≃ Fin tags

variable {K Λ σ : Type} [DecidableEq K] (P : Layout K Λ σ)

def Layout.slot (k : K) : ℕ := 8+(P.tape k).val

theorem Layout.slot_injective : Function.Injective P.slot := fun _ _ h => P.tape.injective (Fin.ext (Nat.add_left_cancel h))

def Layout.tag (l : Option Λ) (q : σ) := l.elim 0 (fun l => 1+(P.control (l,q)).val)

theorem Layout.tag_le (l : Option Λ) (q : σ) : P.tag l q ≤ P.tags := by
  cases l with
  | none => exact Nat.zero_le _
  | some v => change 1+(P.control (v,q)).val ≤ P.tags; have := (P.control (v,q)).isLt; omega

structure Layout.Stacks (s : Store) (S : K → List Bool) : Prop where
  constants : BinaryStack.Constants s
  value : ∀ k, s.mem (cell (P.slot k)) = packed (S k)

structure Layout.Preserves (s t : Store) : Prop where
  out : t.out = s.out
  read : ∀ i, 8+P.tapes ≤ i → t.mem (cell i) = s.mem (cell i)

theorem Layout.Preserves.refl (s : Store) : P.Preserves s s := ⟨rfl,fun _ _ => rfl⟩

theorem Layout.Preserves.trans {s t u : Store} (h : P.Preserves s t) (g : P.Preserves t u) : P.Preserves s u :=
  ⟨g.out.trans h.out,fun i hi => (g.read i hi).trans (h.read i hi)⟩

private theorem afterOne {s t : Store} {S : K → List Bool} (h : P.Stacks s S) (k : K)
    (ys : List Bool) (v : t.mem (cell (P.slot k)) = packed ys)
    (keep : ∀ i, i ≠ P.slot k → i ≠ 3 → i ≠ 4 → i ≠ 6 → t.mem (cell i) = s.mem (cell i)) (out : t.out = s.out) :
    P.Stacks t (Function.update S k ys) ∧ P.Preserves s t := by
  have ge : 8 ≤ P.slot k := by dsimp [Layout.slot]; omega
  have fixed (a : ℕ) (ha : a < 3 ∨ a=5) : t.mem (cell a) = s.mem (cell a) := keep a (by omega) (by omega) (by omega) (by omega)
  have c : Constants t := ⟨(fixed 1 (by decide)).trans h.constants.one,(fixed 2 (by decide)).trans h.constants.two,
    (fixed 5 (by decide)).trans h.constants.zero⟩
  refine ⟨⟨c,?_⟩,⟨out,?_⟩⟩
  · intro a
    by_cases eq : a=k
    · subst a; simpa using v
    · have base : 8 ≤ P.slot a := by dsimp [Layout.slot]; omega
      simpa only [Function.update_of_ne eq] using (keep _ (P.slot_injective.ne eq) (by omega) (by omega) (by omega)).trans (h.value a)
  · intro i hi
    have bounds := (P.tape k).isLt
    exact keep i (by dsimp [Layout.slot]; omega) (by omega) (by omega) (by omega)

theorem pushStack_exec {τ : Tapes} {b : ℕ} (k : K) (bit : Bool) (S : K → List Bool) (s : Store)
    (h : P.Stacks s S) (fit : s.Fits b) (room : (S k).length+2 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (push (P.slot k) bit) s t j ∧ j ≤ 2 ∧
      P.Stacks t (Function.update S k (bit::S k)) ∧ P.Preserves s t := by
  obtain ⟨t,j,run,cost,val,out,fr⟩ := push_exec (τ := τ) (P.slot k) (by dsimp [Layout.slot]; omega) bit (S k) s
    h.constants (h.value k) fit room
  exact ⟨t,j,run,cost,afterOne P h k _ val (fun i hi _ _ _ => fr _ (by simpa [cell] using hi)) out⟩

def popIf (remove : Bool) (S : K → List Bool) (k : K) := if remove then Function.update S k (S k).tail else S

theorem inspectStack_exec {τ : Tapes} {b : ℕ} (k : K) (remove : Bool) (S : K → List Bool) (s : Store)
    (h : P.Stacks s S) (fit : s.Fits b) (room : (S k).length+3 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (inspect (P.slot k) remove) s t j ∧ j ≤ 5*(b*(5*b+9)+15)+2 ∧
      t.mem (cell 6) = headSymbol (S k) ∧ P.Stacks t (popIf remove S k) ∧ P.Preserves s t := by
  obtain ⟨t,j,run,cost,symbol,val,out,fr⟩ := inspect_exec (τ := τ) (P.slot k) (by dsimp [Layout.slot]; omega) remove (S k) s
    h.constants (h.value k) fit room
  obtain ⟨rep,high⟩ := afterOne P h k _ val fr out
  exact ⟨t,j,run,cost,symbol,by cases remove <;> simpa [popIf] using rep,high⟩

def chooseSymbol (arm : Option Bool → Cmd) : Cmd := .branch (cell 6) (cell 5) (arm none)
  (.branch (cell 6) (cell 1) (arm (some false)) (arm (some true)))

theorem chooseSymbol_exec {τ : Tapes} {I : Store → Prop} (arm : Option Bool → Cmd) (xs : List Bool)
    {s t : Store} {j : ℕ} (c : Constants s) (value : s.mem (cell 6) = headSymbol xs)
    (run : Exec τ I (arm xs.head?) s t j) : ∃ a ≤ j+4, Exec τ I (chooseSymbol arm) s t a := by
  cases xs with
  | nil => exact ⟨_,by omega,.yes (by rw [value,c.zero]; decide) run⟩
  | cons x xs =>
    cases x with
    | false => exact ⟨_,by omega,.no (by rw [value,c.zero]; simp [headSymbol]) (.yes (by rw [value,c.one]; simp [headSymbol]) run)⟩
    | true => exact ⟨_,by omega,.no (by rw [value,c.zero]; simp [headSymbol]) (.no (by rw [value,c.one]; simp [headSymbol]) run)⟩

/-- Writing finite control or dispatch scratch cannot alter any stack word. -/
theorem writeControl (i : ℕ) (hi : i = 0 ∨ i=7) (s : Store) (S : K → List Bool) (h : P.Stacks s S) (x : ℕ) :
    P.Stacks (s.write (cell i) x) S ∧ P.Preserves s (s.write (cell i) x) := by
  have keep (a : ℕ) (ha : a ≠ i) : (s.write (cell i) x).mem (cell a) = s.mem (cell a) := by
    have dif : cell a ≠ cell i := by simpa [cell] using ha
    simp [Store.write,dif]
  exact ⟨⟨⟨(keep 1 (by omega)).trans h.constants.one,(keep 2 (by omega)).trans h.constants.two,
    (keep 5 (by omega)).trans h.constants.zero⟩,fun k => (keep _ (by dsimp [Layout.slot]; omega)).trans (h.value k)⟩,
    ⟨rfl,fun a ha => keep _ (by omega)⟩⟩

end TargetedSamplers.Structured.StackMachine

end TM2RAMStacks

section TM2RAMStatement

namespace TargetedSamplers.Structured.StackMachine

open Word BinaryStack Turing

abbrev Stmt (K Λ σ : Type) := TM2.Stmt (fun _ : K => Bool) Λ σ

abbrev Config (K Λ σ : Type) := TM2.Cfg (fun _ : K => Bool) Λ σ

variable {K Λ σ : Type} [DecidableEq K] (P : Layout K Λ σ)

def depth : Stmt K Λ σ → ℕ
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q => depth q+1
  | .branch _ q r => depth q+depth r+1
  | .goto _ | .halt => 1

/-- Specialize finite local state at compile time. Only a stack observation can select
a runtime arm inside a single TM2 transition. -/
def compile : Stmt K Λ σ → σ → Cmd
  | .push k f q,v => .seq (push (P.slot k) (f v)) (compile q v)
  | .peek k f q,v => .seq (inspect (P.slot k) false) (chooseSymbol fun x => compile q (f v x))
  | .pop k f q,v => .seq (inspect (P.slot k) true) (chooseSymbol fun x => compile q (f v x))
  | .load f q,v => compile q (f v)
  | .branch f q r,v => if f v then compile q v else compile r v
  | .goto f,v => .op (.const (cell 0) (P.tag (some (f v)) v))
  | .halt,_ => .op (.const (cell 0) 0)

def tick (b : ℕ) := 5*(b*(5*b+9)+15)+8

structure Layout.Ends (c : Config K Λ σ) (s t : Store) : Prop where
  rep0 : P.Stacks t c.stk
  label : t.mem (cell 0) = P.tag c.l c.var
  frame : P.Preserves s t

theorem Layout.Ends.pre {c : Config K Λ σ} {s t u : Store} (h : P.Ends c t u) (f : P.Preserves s t) :
    P.Ends c s u := ⟨h.rep0,h.label,Layout.Preserves.trans P f h.frame⟩

private def Correct (d : ℕ) (cmd : σ → Cmd) (effect : σ → (K → List Bool) → Config K Λ σ) : Prop :=
  ∀ {τ : Tapes} {b : ℕ} (v : σ) (S : K → List Bool) (s : Store),
    P.Stacks s S → s.Fits b → P.tags.size ≤ b → (∀ k, (S k).length+d+3 ≤ b) →
    ∃ t j, Exec τ (fun u => u.Fits b) (cmd v) s t j ∧ j ≤ d*tick b ∧ P.Ends (effect v S) s t

private theorem read_correct (k : K) (remove : Bool) (f : σ → Option Bool → σ) (d : ℕ)
    (cmd : σ → Cmd) (effect : σ → (K → List Bool) → Config K Λ σ) (ih : Correct P d cmd effect) :
    Correct P (d+1) (fun v => .seq (inspect (P.slot k) remove) (chooseSymbol fun x => cmd (f v x)))
      (fun v S => effect (f v (S k).head?) (popIf remove S k)) := by
  intro τ b v S s rep0 fit tagW room
  obtain ⟨u,i,read,wi,code,next,high⟩ := inspectStack_exec (τ := τ) P k remove S s rep0 fit (by have := room k; omega)
  have enough (a : K) : ((popIf remove S k) a).length+d+3 ≤ b := by
    have base := room a
    by_cases eq : a=k
    · subst a; cases remove <;> simp [popIf,List.length_tail] <;> omega
    · cases remove <;> simp [popIf,eq] <;> omega
  obtain ⟨t,j,body,wj,post⟩ := ih (τ := τ) (f v (S k).head?) _ u next (read.post fit) tagW enough
  obtain ⟨a,wa,choice⟩ := chooseSymbol_exec (fun x => cmd (f v x)) (S k) next.constants code body
  refine ⟨t,_,read.seq choice,?_,Layout.Ends.pre P post high⟩
  rw [Nat.succ_mul]; dsimp [tick] at *; omega

private theorem finish_correct (l : σ → Option Λ) :
    Correct P 1 (fun v => .op (.const (cell 0) (P.tag (l v) v))) (fun v S => ⟨l v,v,S⟩) := by
  intro τ b v S s rep0 fit bound _
  let tag := P.tag (l v) v
  have f : (s.write (cell 0) tag).Fits b := Store.write_fits fit _ ((Nat.size_le_size (P.tag_le _ _)).trans bound)
  have ⟨rep,high⟩ := writeControl P 0 (Or.inl rfl) s S rep0 tag
  exact ⟨_,1,.op _ _ f,by dsimp [tick]; omega,rep,by simp [Op.eval,Store.write,tag],high⟩

private theorem stmt_correct (p : Stmt K Λ σ) :
    Correct P (depth p) (compile P p) (TM2.stepAux p) := by
  induction p with
  | push k f q ih =>
    intro τ b v S s rep0 fit tagW room
    obtain ⟨u,i,first,wi,rep,high⟩ := pushStack_exec (τ := τ) P k (f v) S s rep0 fit (by have := room k; simp only [depth] at this; omega)
    have enough (a : K) : ((Function.update S k (f v :: S k)) a).length+depth q+3 ≤ b := by
      have base := room a
      simp only [depth] at base
      by_cases eq : a=k
      · subst a; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using base
      · rw [Function.update_of_ne eq]; omega
    obtain ⟨t,j,rest,wj,post⟩ := ih (τ := τ) v _ u rep (first.post fit) tagW enough
    exact ⟨t,_,first.seq rest,by simp only [depth,Nat.succ_mul]; dsimp [tick] at *; omega,Layout.Ends.pre P post high⟩
  | peek k f q ih => exact read_correct P k false f _ _ _ ih
  | pop k f q ih => exact read_correct P k true f _ _ _ ih
  | load f q ih =>
    intro τ b v S s rep0 fit tagW room
    obtain ⟨t,j,run,w,post⟩ := ih (τ := τ) (f v) S s rep0 fit tagW
      (fun a => by have := room a; simp only [depth] at this; omega)
    exact ⟨t,j,run,by simp only [depth,Nat.succ_mul]; omega,post⟩
  | branch f q r iq ir =>
    intro τ b v S s rep0 fit tagW room
    cases h : f v with
    | true =>
      obtain ⟨t,j,run,w,post⟩ := iq (τ := τ) v S s rep0 fit tagW
        (fun a => by have := room a; simp only [depth] at this; omega)
      exact ⟨t,j,by simpa only [compile,h,if_true] using run,
        by simp only [depth,Nat.succ_mul,Nat.add_mul]; omega,by simpa only [TM2.stepAux,h,cond_true] using post⟩
    | false =>
      obtain ⟨t,j,run,w,post⟩ := ir (τ := τ) v S s rep0 fit tagW
        (fun a => by have := room a; simp only [depth] at this; omega)
      exact ⟨t,j,by simpa only [compile,h,Bool.false_eq_true,if_false] using run,
        by simp only [depth,Nat.succ_mul,Nat.add_mul]; omega,by simpa only [TM2.stepAux,h,cond_false] using post⟩
  | goto f => exact finish_correct P (fun v => some (f v))
  | halt => exact finish_correct P (fun _ => none)

theorem compile_exec {τ : Tapes} {b : ℕ} (p : Stmt K Λ σ) (v : σ) (S : K → List Bool) (s : Store)
    (rep0 : P.Stacks s S) (fit : s.Fits b) (tagW : P.tags.size ≤ b)
    (room : ∀ k, (S k).length+depth p+3 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (compile P p v) s t j ∧ j ≤ depth p*tick b ∧ P.Ends (TM2.stepAux p v S) s t :=
  stmt_correct P p v S s rep0 fit tagW room

/-- A transition can perform only a fixed number of pushes on any one stack. -/
theorem stepAux_length (p : Stmt K Λ σ) (v : σ) (S : K → List Bool) (k : K) :
    ((TM2.stepAux p v S).stk k).length ≤ (S k).length + depth p := by
  induction p generalizing v S with
  | push a f q ih =>
    have bound := ih v (Function.update S a (f v::S a))
    change _ ≤ _+(_+1)
    by_cases eq : k=a
    · subst k; simpa [TM2.stepAux,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound
    · simpa only [TM2.stepAux,Function.update_of_ne eq] using bound.trans (by rw [Function.update_of_ne eq]; omega)
  | peek a f q ih => exact (ih (f v (S a).head?) S).trans (by simp [depth])
  | pop a f q ih =>
    have bound := ih (f v (S a).head?) (Function.update S a (S a).tail)
    by_cases eq : k=a
    · subst k; simp only [TM2.stepAux,depth,Function.update_self,List.length_tail] at *; omega
    · simp only [TM2.stepAux,depth,Function.update_of_ne eq] at *; omega
  | load f q ih => exact (ih (f v) S).trans (by simp [depth])
  | branch f q r iq ir =>
    cases h : f v
    · simp only [TM2.stepAux,h,cond_false,depth]; have := ir v S; omega
    · simp only [TM2.stepAux,h,cond_true,depth]; have := iq v S; omega
  | goto | halt => simp [TM2.stepAux,depth]

end TargetedSamplers.Structured.StackMachine

end TM2RAMStatement

section TM2RAMLoop

namespace TargetedSamplers.Structured.StackMachine

open Word BinaryStack Turing

variable {K Λ σ : Type} [DecidableEq K] (P : Layout K Λ σ) (code : Λ → Stmt K Λ σ)

def arms : List Cmd := List.ofFn fun i : Fin P.tags =>
  compile P (code (P.control.symm i).1) (P.control.symm i).2

def body : Cmd := dispatch (cell 0) (cell 7) 1 (arms P code)

def loop : Cmd := .whileGt (cell 0) (cell 5) (body P code)

def capacity : ℕ := ∑ i : Fin P.tags, depth (code (P.control.symm i).1)

theorem depth_le (l : Λ) (v : σ) : depth (code l) ≤ capacity P code := by
  have h := Finset.single_le_sum (f := fun i : Fin P.tags => depth (code (P.control.symm i).1))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (P.control (l,v)))
  simpa [capacity] using h

def stepCost (b : ℕ) := 3*P.tags+4+capacity P code*tick b

theorem body_exec {τ : Tapes} {b : ℕ} (l : Λ) (v : σ) (S : K → List Bool) (s : Store)
    (rep0 : P.Stacks s S) (tag : s.mem (cell 0) = P.tag (some l) v)
    (fit : s.Fits b) (sizeTag : P.tags.size ≤ b)
    (room : ∀ k, (S k).length+capacity P code+3 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (body P code) s t j ∧ j+2 ≤ stepCost P code b ∧
      P.Ends (TM2.stepAux (code l) v S) s t := by
  let i := P.control (l,v)
  let key := 1+i.val
  let u := s.write (cell 7) key
  have top : key ≤ P.tags := by have := i.isLt; dsimp [key]; omega
  have safe (x : ℕ) (hx : x ≤ key) : (s.write (cell 7) x).Fits b :=
    Store.write_fits fit _ ((Nat.size_le_size (hx.trans top)).trans sizeTag)
  obtain ⟨rep,high⟩ := writeControl P 7 (Or.inr rfl) s S rep0 key
  obtain ⟨t,j,run,w,post⟩ := compile_exec (τ := τ) P (code l) v S u rep (safe key le_rfl) sizeTag
    (fun k => by have := room k; have := depth_le P code l v; omega)
  have len : (arms P code).length = P.tags := List.length_ofFn
  let a := i.cast len.symm
  have arm : (arms P code)[a.val] = compile P (code l) v := by
    simp only [arms,List.getElem_ofFn]
    change compile P (code (P.control.symm (P.control (l,v))).1) (P.control.symm (P.control (l,v))).2 = _
    rw [Equiv.symm_apply_apply]
  have sel := dispatch_select (τ := τ) (inv := fun u => u.Fits b) (cell 0) (cell 7) (by decide)
    (arms P code) 1 s t a j tag safe (arm ▸ run)
  refine ⟨t,_,sel,?_,Layout.Ends.pre P post high⟩
  have small := Nat.mul_le_mul_right (tick b) (depth_le P code l v)
  have ia := i.isLt
  change 3*i.val+2+j+2 ≤ 3*P.tags+4+capacity P code*tick b
  omega

private def advance (c : Option (Config K Λ σ)) := c.bind (TM2.step code)

private theorem trace_exec {τ : Tapes} {b : ℕ} (N : ℕ) (c z : Config K Λ σ)
    (trace : (advance code)^[N] (some c) = some z) (halted : z.l = none) (s : Store)
    (rep : P.Stacks s c.stk) (tag : s.mem (cell 0) = P.tag c.l c.var) (fit : s.Fits b)
    (sizeTag : P.tags.size ≤ b) (room : ∀ k, (c.stk k).length+N*capacity P code+3 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (loop P code) s t j ∧ j ≤ N*stepCost P code b+1 ∧ P.Ends z s t := by
  induction N generalizing c s with
  | zero =>
    have eq : c=z := Option.some.inj trace
    subst c
    have hzero : s.mem (cell 0) = 0 := by simp [tag,halted,Layout.tag]
    exact ⟨s,1,Exec.done (by rw [hzero,rep.constants.zero]),by simp,rep,tag,Layout.Preserves.refl P s⟩
  | succ N ih =>
    rw [Function.iterate_succ_apply] at trace
    rcases c with ⟨lc,v,S⟩
    cases lc with
    | none =>
      change (advance code)^[N] none = some z at trace
      rw [Function.iterate_fixed (f := advance code) (x := none) rfl] at trace
      contradiction
    | some l =>
      let c' := TM2.stepAux (code l) v S
      change (advance code)^[N] (some c') = some z at trace
      change ∀ k, (S k).length+(N+1)*capacity P code+3 ≤ b at room
      obtain ⟨u,i,step,wi,post⟩ := body_exec (τ := τ) P code l v S s rep tag fit sizeTag
        (fun k => by have h := room k; rw [Nat.succ_mul] at h; omega)
      obtain ⟨t,j,rest,wj,done⟩ := ih c' trace u post.rep0 post.label (step.post fit) (fun k => by
        have len := stepAux_length (code l) v S k
        have dep := depth_le P code l v
        have h := room k
        rw [Nat.succ_mul] at h
        dsimp [c']; omega)
      have pos : ¬s.mem (cell 0) ≤ s.mem (cell 5) := by
        rw [tag,rep.constants.zero]; change ¬1+_ ≤ 0; omega
      exact ⟨t,_,Exec.again pos step rest,by rw [Nat.succ_mul]; omega,Layout.Ends.pre P done post.frame⟩

/-- Simulate an arbitrary native finite Boolean-stack computation. An N-step run
needs at most the input height plus N times a fixed per-program growth constant. -/
theorem loop_exec {τ : Tapes} {b T : ℕ} (c z : Config K Λ σ)
    (h : StateTransition.EvalsToInTime (TM2.step code) c (some z) T) (halted : z.l = none) (s : Store)
    (rep : P.Stacks s c.stk) (tag : s.mem (cell 0) = P.tag c.l c.var) (fit : s.Fits b)
    (sizeTag : P.tags.size ≤ b) (room : ∀ k, (c.stk k).length+T*capacity P code+3 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (loop P code) s t j ∧ j ≤ T*stepCost P code b+1 ∧ P.Ends z s t := by
  obtain ⟨t,j,run,w,post⟩ := trace_exec (τ := τ) P code h.steps c z h.evals_in_steps halted s rep tag fit sizeTag
    (fun k => by have := room k; have := Nat.mul_le_mul_right (capacity P code) h.steps_le_m; omega)
  exact ⟨t,j,run,w.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h.steps_le_m) 1),post⟩

end TargetedSamplers.Structured.StackMachine

end TM2RAMLoop

section TM2RAMInit

namespace TargetedSamplers.Structured.StackMachine

open Word BinaryStack Turing

variable {K Λ σ : Type} [DecidableEq K] (P : Layout K Λ σ)

/-- Initialize the finite stack window, including words left over from an earlier call. -/
def wipe : ℕ → Cmd
  | 0 => .skip
  | n+1 => .seq (wipe n) (.op (.const (cell (8+n)) 1))

private theorem wipe_exec {τ : Tapes} {b : ℕ} (n : ℕ) (s : Store) (fit : s.Fits b) (hb : 2 ≤ b) :
    ∃ t, Exec τ (fun u => u.Fits b) (wipe n) s t n ∧ t.out = s.out ∧
      ∀ i, t.mem (cell i) = if 8 ≤ i ∧ i < 8+n then 1 else s.mem (cell i) := by
  induction n with
  | zero => exact ⟨s,.skip s,rfl,fun i => by split <;> first | omega | rfl⟩
  | succ n ih =>
    obtain ⟨u,first,out,mem⟩ := ih
    let t := u.write (cell (8+n)) 1
    have fits : t.Fits b := Store.write_fits (first.post fit) _ (by change 1 ≤ b; omega)
    have last : Exec τ (fun u => u.Fits b) (.op (.const (cell (8+n)) 1)) u t 1 := .op _ _ fits
    refine ⟨t,first.seq last,out,?_⟩
    intro i
    by_cases eq : i=8+n
    · subst i; simp [t,Store.write]
    · have dif : cell i ≠ cell (8+n) := by simpa [cell] using eq
      rw [show t.mem (cell i) = u.mem (cell i) by simp [t,Store.write,dif],mem]
      split <;> split <;> first | omega | rfl

def header (inputSlot source tag : ℕ) : Fragment := Structured.sequence [
  .op (.const (cell 1) 1),.op (.const (cell 2) 2),.op (.const (cell 5) 0),
  .op (.const (cell 0) tag),.op (.add (cell inputSlot) (cell source) (cell 5))]

def initializeStacks (input : K) (main : Λ) (v : σ) (source : ℕ) : Cmd :=
  .seq (wipe P.tapes) (header (P.slot input) source (P.tag (some main) v)).cmd

set_option maxHeartbeats 500000 in
theorem initialize_exec {τ : Tapes} {b : ℕ} (input : K) (main : Λ) (v : σ) (source : ℕ)
    (high : 8+P.tapes ≤ source) (bits : List Bool) (s : Store) (stored : s.mem (cell source) = packed bits)
    (fit : s.Fits b) (hb : 2 ≤ b) (sizeTag : P.tags.size ≤ b) :
    ∃ t, Exec τ (fun u => u.Fits b) (initializeStacks P input main v source) s t (P.tapes+5) ∧
      P.Stacks t (fun k => if k=input then bits else []) ∧ t.mem (cell 0) = P.tag (some main) v ∧ P.Preserves s t := by
  obtain ⟨u,clear,out,mem⟩ := wipe_exec (τ := τ) P.tapes s fit hb
  let tag := P.tag (some main) v
  let dst := P.slot input
  have lo : 8 ≤ dst := by simp [dst,Layout.slot]
  have bound : dst < 8+P.tapes := by have := (P.tape input).isLt; dsimp [dst,Layout.slot]; omega
  have fixed (i j : ℕ) (h : i ≠ j) : cell i ≠ cell j := by simpa [cell] using h
  have hsrc (j : ℕ) (hj : j < 8+P.tapes) : cell source ≠ cell j := fixed _ _ (by omega)
  have hdst (j : ℕ) (hj : j < 8) : cell dst ≠ cell j := fixed _ _ (by omega)
  have low (j : ℕ) (hj : j < 8) : cell j ≠ cell dst := Ne.symm (hdst j hj)
  have cellEq (i j : ℕ) : (cell i = cell j) ↔ i=j := by simp [cell]
  have one : 1 ≤ b := by omega
  have htag : tag.size ≤ b := (Nat.size_le_size (P.tag_le _ _)).trans sizeTag
  let f := header dst source tag
  let t := (f.run τ u).last
  have unit : (1:ℕ).size ≤ b := by change 1 ≤ b; omega
  have two : (2:ℕ).size ≤ b := hb
  have src : u.mem (cell source) = packed bits := (mem source).trans (by rw [if_neg (by omega)]; exact stored)
  have w : (f.run τ u).writeWidth ≤ b := by
    simp (disch := omega) [f,header,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,
      hsrc,cellEq,htag,one,unit,two,(clear.post fit) (cell source)]
  have lowVal (i : ℕ) (hi : i < 8) : t.mem (cell i) =
      if i=0 then tag else if i=5 then 0 else if i=2 then 2 else if i=1 then 1 else u.mem (cell i) := by
    simp (disch := omega) [t,f,header,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
      low _ hi,cellEq]
  have stackVal (i : ℕ) (hi : 8 ≤ i) : t.mem (cell i) = if i=dst then packed bits else u.mem (cell i) := by
    have large (j : ℕ) (hj : j < 8) : cell i ≠ cell j := fixed _ _ (by omega)
    by_cases eq : i=dst
    · subst i
      simp (disch := omega) [t,f,header,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,hsrc,cellEq,src]
    · simp (disch := omega) [t,f,header,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,
        large,fixed _ _ eq,eq]
  have headRun : Exec τ (fun st => st.Fits b) f.cmd u t 5 := f.exec τ u b (clear.post fit) w
  refine ⟨t,clear.seq headRun,⟨⟨by simpa using lowVal 1 (by decide),by simpa using lowVal 2 (by decide),
    by simpa using lowVal 5 (by decide)⟩,?_⟩,by simpa [tag] using lowVal 0 (by decide),⟨out,?_⟩⟩
  · intro k
    have ge : 8 ≤ P.slot k := by simp [Layout.slot]
    have lt : P.slot k < 8+P.tapes := by dsimp [Layout.slot]; have := (P.tape k).isLt; omega
    rw [stackVal _ ge]
    by_cases eq : k=input
    · subst k; simp [dst]
    · simp [dst,P.slot_injective.ne eq,eq,mem,ge,lt]
  · intro i hi
    rw [stackVal i (by omega),if_neg (by omega),mem,if_neg (by omega)]

end TargetedSamplers.Structured.StackMachine

end TM2RAMInit

section NativePolynomialLogCostRAM

namespace TargetedSamplers.Structured.StackMachine

open Word BinaryStack OAI.MetricKMedian.Binary Turing

noncomputable def layout (M : Machine) : Layout M.K M.Label M.State :=
  ⟨Fintype.card M.K,Fintype.card (M.Label × M.State),Fintype.equivFin _,Fintype.equivFin _⟩

noncomputable def call (M : Machine) (source : ℕ) : Cmd :=
  .seq (initializeStacks (layout M) M.input M.main M.initial source) (loop (layout M) M.code)

/-- Bound the true run of a native polynomial-time kernel in a caller's RAM store.
The caller supplies the packed input at a fixed register above the kernel's stack window. -/
theorem call_exec {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β} (p : PolyProgram ea eb f)
    {τ : Tapes} {b : ℕ} (a : α) (s : Store) (source : ℕ)
    (high : 8+(layout p.machine).tapes ≤ source) (stored : s.mem (cell source) = packed (ea a))
    (fit : s.Fits b) (sizeTag : (layout p.machine).tags.size ≤ b)
    (room : (ea a).length+p.time.eval (ea a).length*capacity (layout p.machine) p.machine.code+3 ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (call p.machine source) s t j ∧
      j ≤ (layout p.machine).tapes+6+p.time.eval (ea a).length*stepCost (layout p.machine) p.machine.code b ∧
      t.mem (cell ((layout p.machine).slot p.machine.output)) = packed (eb (f a)) ∧ (layout p.machine).Preserves s t := by
  let M := p.machine
  let P := layout M
  change (ea a).length+p.time.eval (ea a).length*capacity P M.code+3 ≤ b at room
  have hb : 2 ≤ b := by omega
  obtain ⟨u,init,rep,tag,high0⟩ := initialize_exec (τ := τ) P M.input M.main M.initial source high (ea a) s stored fit hb sizeTag
  have trace : StateTransition.EvalsToInTime (TM2.step M.code) (M.initialCfg (ea a)) (some (M.finalCfg (eb (f a))))
      (p.time.eval (ea a).length) := p.outputs a
  obtain ⟨t,j,run,w,post⟩ := loop_exec (τ := τ) P M.code _ _ trace rfl u rep tag (init.post fit) sizeTag (fun k => by
    change ((if k=M.input then ea a else []) : List Bool).length+_+3 ≤ b
    split <;> first | exact room | simp only [List.length_nil,Nat.zero_add]; omega)
  have val := post.rep0.value M.output
  change t.mem (cell (P.slot M.output)) = packed (if M.output=M.output then eb (f a) else []) at val
  exact ⟨t,_,init.seq run,by dsimp [M,P] at *; omega,by simpa [P,M] using val,Layout.Preserves.trans P high0 post.frame⟩

/-- A caller can raise the word-width bound to accommodate its own addresses and
live data. The fixed machine's work remains polynomial in that chosen width. -/
theorem polynomial_call {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β} (p : PolyProgram ea eb f) :
    ∃ (kernel : Cmd) (source output : ℕ) (width steps : Polynomial ℕ),
      ∀ (a : α) (τ : Tapes) (s : Store) (b : ℕ), width.eval (ea a).length ≤ b →
      s.mem (cell source) = packed (ea a) → s.Fits b →
      ∃ t j, Exec τ (fun u => u.Fits b) kernel s t j ∧ j ≤ steps.eval b ∧
        t.mem (cell output) = packed (eb (f a)) ∧ t.out = s.out ∧
        ∀ i, source ≤ i → t.mem (cell i) = s.mem (cell i) := by
  let M := p.machine
  let P := layout M
  let src := 8+P.tapes
  let w : Polynomial ℕ := Polynomial.X + p.time * Polynomial.C (capacity P M.code) + p.time + 3 + Polynomial.C P.tags.size
  let x : Polynomial ℕ := Polynomial.X
  let d : Polynomial ℕ := 3 * Polynomial.C P.tags + 4 + Polynomial.C (capacity P M.code) * (5*(x*(5*x+9)+15)+8)
  let jmax : Polynomial ℕ := Polynomial.C (P.tapes+6) + x*d
  refine ⟨call M src,src,P.slot M.output,w,jmax,?_⟩
  intro a τ s b enough stored fit
  let L := (ea a).length
  have width : w.eval L = L+p.time.eval L*capacity P M.code+p.time.eval L+3+P.tags.size := by simp [w]
  change w.eval L ≤ b at enough
  rw [width] at enough
  obtain ⟨t,j,ex,time,out,frame⟩ := call_exec (τ := τ) p a s src le_rfl stored fit
    (by change P.tags.size ≤ b; omega)
    (by change L+p.time.eval L*capacity P M.code+3 ≤ b; omega)
  have step : d.eval b = stepCost P M.code b := by simp [d,x,stepCost,tick]
  have total : jmax.eval b = P.tapes+6+b*stepCost P M.code b := by simp [jmax,x,step]
  change j ≤ P.tapes+6+p.time.eval L*stepCost P M.code b at time
  exact ⟨t,j,ex,by rw [total]; exact time.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : p.time.eval L ≤ b)) _),
    out,frame.out,frame.read⟩

end TargetedSamplers.Structured.StackMachine

end NativePolynomialLogCostRAM

section UnpackNativeNatural

namespace TargetedSamplers.Structured.BinaryStack

/-- Remove the high sentinel from a native natural-number result. During doubling,
the remaining distance is compared to the current power, so intermediate words
never exceed the input even when its highest bit is the last bit that fits. -/
private def stripStep (src : ℕ) : Fragment := Structured.sequence [
  .op (.add 0 0 0),.op (.sub 1 src 0),.op (.add 1 1 2)]

private def stripInit (src : ℕ) : Fragment := Structured.sequence [
  .op (.const 0 1),.op (.const 2 1),.op (.sub 1 src 0),.op (.add 1 1 2)]

def unpackNatural (src : ℕ) : Cmd := .seq (stripInit src).cmd
  (.seq (.whileGt 1 0 (stripStep src).cmd) (.op (.sub 0 src 0)))

private theorem strip_loop {τ : Tapes} {b x d src : ℕ} (low : 3 ≤ src)
    (lower : 2^d ≤ x) (upper : x < 2^(d+1)) (s : Store) (i left : ℕ) (depth : i+left=d)
    (value : s.mem src=x) (power : s.mem 0=2^i) (threshold : s.mem 1=x-2^i+1)
    (one : s.mem 2=1) (fit : s.Fits b) :
    ∃ t, Exec τ (fun u => u.Fits b) (.whileGt 1 0 (stripStep src).cmd) s t (5*left+1) ∧
      t.mem 0=2^d ∧ t.out=s.out ∧ ∀ a ≥ 2, t.mem a=s.mem a := by
  induction left generalizing i s with
  | zero =>
    have last : i=d := by omega
    subst i
    rw [pow_succ] at upper
    exact ⟨s,.done (by rw [threshold,power];omega),power,rfl,fun _ _ => rfl⟩
  | succ left ih =>
    have nextLe := (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : i+1 ≤ d)).trans lower
    have grow : 2^i+2^i=2^(i+1) := by rw [pow_succ];omega
    have nextPos := Nat.two_pow_pos (i+1)
    have hw (a : ℕ) (ha : a ≤ x) : a.size ≤ b := (Nat.size_le_size ha).trans (value ▸ fit src)
    have pw := hw _ nextLe
    have sub := hw _ (Nat.sub_le x (2^(i+1)))
    have offset := hw (x-2^(i+1)+1) (by omega)
    have far (a : ℕ) (ha : a < 3) : src ≠ a := by omega
    let t := ((stripStep src).run τ s).last
    have ww : ((stripStep src).run τ s).writeWidth ≤ b := by
      simp (disch := omega) [stripStep,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,
        Function.update_apply,far,value,power,one,grow,pw,sub,offset]
    have step : Exec τ (fun u => u.Fits b) (stripStep src).cmd s t 3 := (stripStep src).exec τ s b fit ww
    have high (a : ℕ) (ha : 2 ≤ a) : t.mem a=s.mem a := by
      simp (disch := omega) [t,stripStep,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply]
    have now : t.mem 0=2^(i+1) := by simp [t,stripStep,Structured.sequence,Fragment.run,Op.eval,Store.write,power,grow]
    have th : t.mem 1=x-2^(i+1)+1 := by
      simp (disch := omega) [t,stripStep,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,far,
        value,power,one,grow]
    obtain ⟨z,run,result,out,save⟩ := ih t (i+1) (by omega) ((high src (by omega)).trans value)
      now th ((high 2 (by decide)).trans one) (step.post fit)
    have go : ¬s.mem 1 ≤ s.mem 0 := by rw [threshold,power];rw [pow_succ] at nextLe;omega
    exact ⟨z,by simpa only [show 5*(left+1)+1=1+3+1+(5*left+1) by omega] using Exec.again go step run,
      result,out,fun a ha => (save a ha).trans (high a ha)⟩

theorem unpackNatural_exec {τ : Tapes} {b : ℕ} (src x : ℕ) (low : 3 ≤ src) (u : Store)
    (input : u.mem src=packed x.bits) (fit : u.Fits b) :
    ∃ t, Exec τ (fun s => s.Fits b) (unpackNatural src) u t (5*x.size+6) ∧
      t.mem 0=x ∧ t.out=u.out ∧ ∀ a ≥ 3, t.mem a=u.mem a := by
  let v := x+2^x.size
  have stored : u.mem src=v := input.trans (packed_nat_bits x)
  have lowPow : 2^x.size ≤ v := by dsimp [v];omega
  have highPow : v < 2^(x.size+1) := by dsimp [v];rw [pow_succ];have := Nat.lt_size_self x;omega
  have pos := Nat.two_pow_pos x.size
  have far (a : ℕ) (ha : a < 3) : src ≠ a := by omega
  have w := stored ▸ fit src
  have oneW : (1:ℕ).size ≤ b := (Nat.size_le_size (by omega : 1 ≤ v)).trans w
  have subW : (v-1).size ≤ b := (Nat.size_le_size (Nat.sub_le v 1)).trans w
  have th : v-1+1=v := by omega
  let s := ((stripInit src).run τ u).last
  have ww : ((stripInit src).run τ u).writeWidth ≤ b := by
    simp (disch := omega) [stripInit,Structured.sequence,Fragment.run,Op.eval,Op.written,Store.write,Function.update_apply,
      far,stored,oneW,subW,th,w]
    all_goals exact oneW
  have init : Exec τ (fun s => s.Fits b) (stripInit src).cmd u s 4 := (stripInit src).exec τ u b fit ww
  have keep (a : ℕ) (ha : 3 ≤ a) : s.mem a=u.mem a := by
    simp (disch := omega) [s,stripInit,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply]
  have cur : s.mem 0=1 := by simp [s,stripInit,Structured.sequence,Fragment.run,Op.eval,Store.write]
  have threshold : s.mem 1=v := by
    simp (disch := omega) [s,stripInit,Structured.sequence,Fragment.run,Op.eval,Store.write,Function.update_apply,far,stored,th]
  have one : s.mem 2=1 := by simp [s,stripInit,Structured.sequence,Fragment.run,Op.eval,Store.write]
  obtain ⟨z,loop,highest,out,frame⟩ := strip_loop (τ := τ) low lowPow highPow s 0 x.size (by simp)
    ((keep _ low).trans stored) (by simpa using cur) (by simpa [th] using threshold) one (init.post fit)
  have zsrc := (frame src (by omega)).trans ((keep _ low).trans stored)
  have ev : (Op.sub 0 src 0).eval τ z=z.write 0 x := by simp [Op.eval,zsrc,v,highest]
  have wx : x.size ≤ b := (Nat.size_le_size (by dsimp [v]; omega : x ≤ v)).trans w
  have last : Exec τ (fun s => s.Fits b) (.op (.sub 0 src 0)) z (z.write 0 x) 1 := by
    simpa only [ev] using (Exec.op (τ := τ) (inv := fun s => s.Fits b) z (.sub 0 src 0)
      (by rw [ev];exact Store.write_fits (loop.post (init.post fit)) _ wx))
  refine ⟨z.write 0 x,?_,by simp [Store.write],out,?_⟩
  · unfold unpackNatural
    rw [show 5*x.size+6=4+(5*x.size+1+1) by omega]
    exact init.seq (loop.seq last)
  · intro a ha
    simpa [Store.write,show a ≠ 0 by omega] using (frame a (by omega)).trans (keep a ha)

end TargetedSamplers.Structured.BinaryStack

end UnpackNativeNatural

section LogCostRAMPackFields

namespace TargetedSamplers.Structured.Word

open NumericFields

private def prependField (dst radix src : ℕ) : List Assignment := [
  ⟨dst,.arithmetic .mul radix dst⟩,⟨dst,.add src dst⟩]

private theorem prependField_exec {τ : Tapes} {b : ℕ} (dst radix src r dig acc : ℕ) (s : Store)
    (sep : src ≠ dst) (base : s.mem (cell radix)=r) (input : s.mem (cell src)=dig) (top : s.mem (cell dst)=acc)
    (fit : s.Fits b) (hb : 2 ≤ b) (radixW : (2*r+2).size ≤ b) (room : (dig+r*acc).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (Circuit.cmd (prependField dst radix src)) s t j ∧
      j ≤ 2*(b*(5*b+9)+15) ∧ t.mem (cell dst)=dig+r*acc ∧ t.out=s.out ∧
      ∀ a, a ≠ dst → t.mem (cell a)=s.mem (cell a) := by
  let v := fun i => s.mem (cell i)
  have rad : v radix=r := base
  have word : v src=dig := input
  have old : v dst=acc := top
  have mw := (Nat.size_le_size (show r*acc ≤ dig+r*acc by omega)).trans room
  have width : Circuit.width v (prependField dst radix src) ≤ b := by
    simp [prependField,Circuit.width,Assignment.update,Expression.width,Expression.eval,Function.update_apply,
      Arithmetic.value,sep,rad,word,old,max_le_iff,mw,room,radixW]
  obtain ⟨t,j,run,cost,rep,out⟩ := Circuit.exec (τ := τ) (prependField dst radix src) v s (fun _ => rfl) fit hb width
  have bound := cost.trans (Circuit.steps_le _ _ _ width)
  have mult : Circuit.multiplicity v (prependField dst radix src)=2 := rfl
  rw [mult] at bound
  refine ⟨t,j,run,bound,?_,out,?_⟩
  · rw [rep];simp [prependField,Circuit.result,Assignment.update,Expression.eval,Function.update_apply,
      Arithmetic.value,sep,rad,word,old]
  · intro i hi
    rw [rep]
    exact Circuit.result_untouched _ _ _ (by intro item h; simp only [prependField,List.mem_cons,List.not_mem_nil,or_false] at h;
                                             rcases h with rfl|rfl <;> exact hi)

def packFields (dst radix : ℕ) : List ℕ → Cmd
  | [] => .op (.const (cell dst) 3)
  | i::more => .seq (packFields dst radix more) (Circuit.cmd (prependField dst radix i))

/-- Pack a fixed register list in binary. Large fields are charged by bit width;
the program takes a fixed number of multiplications independently of their values. -/
theorem packFields_exec {τ : Tapes} {b : ℕ} (dst radix : ℕ) (regs : List ℕ) (r : ℕ) (s : Store)
    (base : s.mem (cell radix)=r) (pos : 0 < r) (safe : radix ≠ dst ∧ ∀ i∈regs,i ≠ dst)
    (fit : s.Fits b) (hb : 2 ≤ b) (radixW : (2*r+2).size ≤ b)
    (room : (join r (regs.map (fun i => s.mem (cell i))) 3).size ≤ b) :
    ∃ t j, Exec τ (fun u => u.Fits b) (packFields dst radix regs) s t j ∧
      j ≤ regs.length*(2*(b*(5*b+9)+15))+1 ∧ t.mem (cell dst)=join r (regs.map (fun i => s.mem (cell i))) 3 ∧
      t.out=s.out ∧ ∀ a, a ≠ dst → t.mem (cell a)=s.mem (cell a) := by
  induction regs with
  | nil =>
    let t := s.write (cell dst) 3
    have f : t.Fits b := Store.write_fits fit _ hb
    exact ⟨t,1,.op _ _ f,by simp,by simp [t,Store.write,join],rfl,fun a h => by simp [t,Store.write,cell,h]⟩
  | cons i more ih =>
    let tail := join r (more.map (fun i => s.mem (cell i))) 3
    let dig := s.mem (cell i)
    change (dig+r*tail).size ≤ b at room
    have rest : tail ≤ r*tail := by simpa using Nat.mul_le_mul_right tail pos
    obtain ⟨u,k,first,wk,old,out,keep⟩ := ih ⟨safe.1,fun a ha => safe.2 a (by simp [ha])⟩
      ((Nat.size_le_size (by omega : tail ≤ dig+r*tail)).trans room)
    have src := safe.2 i (by simp)
    obtain ⟨t,j,add,wj,val,ret,frame⟩ := prependField_exec (τ := τ) dst radix i r dig tail u src
      ((keep _ safe.1).trans base) (keep _ src) old (first.post fit) hb radixW room
    exact ⟨t,_,first.seq add,by rw [List.length_cons,Nat.succ_mul more.length]; omega,val,ret.trans out,
      fun a ha => (frame a ha).trans (keep a ha)⟩

end TargetedSamplers.Structured.Word

end LogCostRAMPackFields

section NativeFieldRAMCall

namespace TargetedSamplers.Structured.StackMachine

open Word BinaryStack NumericFields

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- A native polynomial natural-number function can be called in log-cost RAM
with a packed input and returns an ordinary natural in register zero. -/
theorem nat_call (f : ℕ → ℕ) (poly : Poly f) :
    ∃ (kernel : Cmd) (source : ℕ) (width steps : Polynomial ℕ), ∀ z (τ : Tapes) (s : Store) b,
      width.eval z.size ≤ b → s.mem (cell source)=packed z.bits → s.Fits b →
      ∃ t k, Exec τ (fun u => u.Fits b) kernel s t k ∧ k ≤ steps.eval b ∧ t.mem 0=f z ∧ t.out=s.out ∧
        ∀ i ≥ source, t.mem (cell i)=s.mem (cell i) := by
  obtain ⟨kernel,src,out,w,p,run⟩ := polynomial_call poly.program
  let total := p+5*Polynomial.X+6
  refine ⟨.seq kernel (unpackNatural (cell out)),src,w,total,?_⟩
  intro z τ s b room input fit
  obtain ⟨v,k,call,work,result,ret,frame⟩ := run z τ s b (by
    change w.eval z.bits.length ≤ b;simpa only [Nat.size_eq_bits_len] using room) input fit
  change v.mem (cell out)=packed (f z).bits at result
  have fv := call.post fit
  have wd : (f z).size+1 ≤ b := by
    have := fv (cell out);rwa [result,packed_size,Nat.size_eq_bits_len] at this
  obtain ⟨t,strip,value,out',keep⟩ := unpackNatural_exec (τ := τ) (cell out) (f z) (by dsimp [cell];omega) v result fv
  refine ⟨t,_,call.seq strip,?_,value,out'.trans ret,fun i hi => (keep _ (by dsimp [cell];omega)).trans (frame i hi)⟩
  rw [show total.eval b=p.eval b+5*b+6 by simp [total]]
  omega

def fieldIndices (bank count : ℕ) := (List.range count).map fun i => bank+i

end TargetedSamplers.Structured.StackMachine

end NativeFieldRAMCall

section
open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.StackMachine
open Word BinaryStack NumericFields
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem solution (f : ℕ → ℕ) (poly : Poly f) (count : ℕ) (hn : 1 ≤ count) :
    ∃ (floor : ℕ) (cmd : ℕ → Cmd) (width steps : Polynomial ℕ), ∀ (bank w : ℕ) (xs : List ℕ)
      (len : xs.length=count) (valid : ∀ x∈xs,x < 2^w) (τ : Tapes) (s : Store) (b : ℕ),
      floor ≤ bank → width.eval w ≤ b → s.Fits b → s.mem (cell (bank+count))=2^w →
      (∀ i (hi : i < count), s.mem (cell (bank+i))=xs[i]'(by omega)) →
      ∃ t k, Exec τ (fun u => u.Fits b) (cmd bank) s t k ∧ k ≤ steps.eval b ∧ t.mem 0=f (pack w xs) ∧
        t.out=s.out ∧ ∀ i ≥ floor, t.mem (cell i)=s.mem (cell i) := by
  obtain ⟨kernel,src,wid,p,run⟩ := nat_call f poly
  let x : Polynomial ℕ := Polynomial.X
  let L : Polynomial ℕ := Polynomial.C count*x+1
  let required := wid.comp L+L+x+4
  let bound := p+Polynomial.C count*(2*(x*(5*x+9)+15))+1
  refine ⟨src+1,(fun bank => .seq (packFields src (bank+count) (fieldIndices bank count)) kernel),required,bound,?_⟩
  intro bank w xs len valid τ s b high enough fit radix data
  let z := pack w xs
  have length : z.size=count*w+1 := by simpa [z,len,Nat.mul_comm] using pack_size w xs valid
  have enough' : wid.eval (count*w+1)+(count*w+1)+w+4 ≤ b := by simpa [required,L,x,Polynomial.eval_comp] using enough
  have input : (fieldIndices bank count).map (fun i => s.mem (cell i))=xs := by
    apply List.ext_getElem
    · simp [fieldIndices,len]
    · intro i h h'
      have hi : i < count := by simpa [fieldIndices] using h
      simpa [fieldIndices,List.getElem_range] using data i hi
  have noAlias : (bank+count) ≠ src ∧ ∀ i∈fieldIndices bank count,i ≠ src := by
    refine ⟨by omega,?_⟩
    intro i hi
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hi
    omega
  have radixSize : (2*2^w+2).size ≤ b := by
    have pos := Nat.two_pow_pos w
    have less : 2*2^w+2 < 2^(w+3) := by rw [pow_add];norm_num;omega
    exact (Nat.size_le.mpr less).trans (by omega)
  have packedInput : join (2^w) xs 3=packed z.bits := by
    change join (2^w) xs 3=packed (pack w xs).bits
    rw [native_packed,packed_nat_bits,pack_size w xs valid]
  have packedWidth : (join (2^w) ((fieldIndices bank count).map (fun i => s.mem (cell i))) 3).size ≤ b := by
    rw [input,packedInput,packed_size,Nat.size_eq_bits_len,length];omega
  obtain ⟨u,j,first,used,request,out,frame⟩ := packFields_exec (τ := τ) src (bank+count) (fieldIndices bank count)
    (2^w) s radix (Nat.two_pow_pos _) noAlias fit (by omega) radixSize packedWidth
  rw [input,packedInput] at request
  obtain ⟨t,k,call,work,answer,ret,save⟩ := run z τ u b (by rw [length];omega) request (first.post fit)
  refine ⟨t,_,first.seq call,?_,answer,ret.trans out,fun i hi => (save i (by omega)).trans (frame i (by omega))⟩
  have size : (fieldIndices bank count).length=count := by simp [fieldIndices]
  rw [size] at used
  rw [show bound.eval b = p.eval b+count*(2*(b*(5*b+9)+15))+1 by simp [bound,x]]
  omega
end
