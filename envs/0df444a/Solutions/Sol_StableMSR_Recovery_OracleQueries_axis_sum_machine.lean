-- Prove2me | solution 1 for StableMSR.Recovery.OracleQueries.axis_sum_machine
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:29:39.857113+00:00
-- url     : https://prove2.me/submissions/6ffd91f1-77e4-43b8-b6e2-2ec2c1ce6b97

import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_while_execution
import Definitions.Def_StableMSR_OracleQueries
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private lemma axSmall (a : Axis) : a.reg < 3 := by cases a <;> decide
private lemma keepReady {x : World} {b : ℕ} {s t : Store} (hb : 3 ≤ b) (h : Keeps b s t) (r : Ready x s) : Ready x t :=
  ⟨fun a=>(h.1 _ (lt_of_lt_of_le (axSmall a) hb)).1.trans (r.1 a),fun i=>by rw [h.2];exact r.2 i⟩
private lemma keepTrans {b : ℕ} {u v t : Store} (h : Keeps b u v) (k : Keeps b v t) : Keeps b u t :=
  ⟨fun i hi=>⟨(k.1 i hi).1.trans (h.1 i hi).1,(k.1 i hi).2.trans (h.1 i hi).2⟩,k.2.trans h.2⟩
private lemma keepDown {b c : ℕ} {s t : Store} (h : Keeps c s t) (le : b ≤ c) : Keeps b s t :=
  ⟨fun i hi=>h.1 i (lt_of_lt_of_le hi le),h.2⟩

theorem solution (a : Axis) (f : Term) (h : Engine f) :
    Engine (fun x ρ=>∑i ∈ Finset.range (x.size a), f x (push i ρ)) := by
  classical
  obtain ⟨p,hp⟩ := h
  refine ⟨(X+1)*(p+C 5)+C 8,?_⟩
  intro b src hb hs
  let lim := b+1
  let idx := b+2
  let tmp := b+3
  obtain ⟨term,eval⟩ := hp tmp (push idx src) (by dsimp [tmp];omega) (fun j=>by
    cases j with
    | zero => dsimp [push,idx,tmp];omega
    | succ j => dsimp [push,tmp];have:=hs j;omega)
  let op₁ := Op.pointerCopy lim a.reg
  let op₂ := Op.pointerDec lim
  let op₃ := Op.pointerConst idx 0
  let op₄ := Op.pointerConst b 0
  let op₅ := Op.realConst b 0
  let addi := Op.pointerAdd b b tmp
  let addr := Op.realAdd b b tmp
  let inc := Op.pointerInc idx
  let body := Cmd.seq term (.seq (.atom addi) (.seq (.atom addr) (.atom inc)))
  let guard := Cond.pointerLE idx lim
  refine ⟨.seq (.atom op₁) (.seq (.atom op₂) (.seq (.atom op₃) (.seq (.atom op₄) (.seq (.atom op₅) (.whileDo guard body))))),?_⟩
  intro x s ρ ready reads
  let N := x.size a
  let part (i : ℕ) := ∑j ∈ Finset.range i,f x (push j ρ)
  let A (i : ℕ) (v : Store) := v.ptrs idx=(i:ℤ) ∧ v.ptrs lim=(N:ℤ)-1 ∧
    (v.ptrs b,v.regs b)=part i ∧ Keeps b s v
  let u := op₅.eval x.dist (op₄.eval x.dist (op₃.eval x.dist (op₂.eval x.dist (op₁.eval x.dist s))))
  have start : A 0 u := by
    dsimp only [A]
    have v := ready.1 a
    refine ⟨?_,?_,?_,⟨?_,rfl⟩⟩
    · simp [u,op₁,op₂,op₃,op₄,op₅,Op.eval,idx,lim]
    · simp [u,op₁,op₂,op₃,op₄,op₅,Op.eval,idx,lim,v,N]
    · simp [u,op₁,op₂,op₃,op₄,op₅,Op.eval,part]
    · intro j hj
      simp [u,op₁,op₂,op₃,op₄,op₅,Op.eval,idx,lim,show j ≠ b+2 by omega,show j ≠ b+1 by omega,ne_of_lt hj]
  have hl : BoundedSum.LoopBound x.dist body guard A N (p.eval x.cap+3) := by
    constructor
    · intro i v av
      change v.ptrs idx ≤ v.ptrs lim ↔ i < N
      rw [av.1,av.2.1];omega
    · intro i hi v av
      obtain ⟨vi,vl,vs,k⟩ := av
      have args (j : ℕ) : v.ptrs (push idx src j)=(push i ρ j:ℤ) := by
        cases j with
        | zero => exact vi
        | succ j => exact (k.1 _ (hs j)).1.trans (reads j)
      obtain ⟨v₁,z,ez,kz,vz,tz⟩ := eval x v (push i ρ) (keepReady hb k ready) args
      let v₂ := addi.eval x.dist v₁
      let v₃ := addr.eval x.dist v₂
      let v₄ := inc.eval x.dist v₃
      have id₁ := (kz.1 idx (by dsimp [idx,tmp];omega)).1.trans vi
      have li₁ := (kz.1 lim (by dsimp [lim,tmp];omega)).1.trans vl
      have acc := kz.1 b (by dsimp [tmp];omega)
      have ai := acc.1.trans (congrArg Prod.fst vs)
      have ar := acc.2.trans (congrArg Prod.snd vs)
      have zi : v₁.ptrs tmp=(f x (push i ρ)).1 := congrArg Prod.fst vz
      have zr : v₁.regs tmp=(f x (push i ρ)).2 := congrArg Prod.snd vz
      have ne₁ : idx ≠ b := by dsimp [idx];omega
      have ne₂ : lim ≠ idx := by dsimp [lim,idx];omega
      have ne₃ : lim ≠ b := by dsimp [lim];omega
      refine ⟨v₄,_,Executes.seq ez (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))),by omega,?_,?_,?_,⟨?_,kz.2.trans k.2⟩⟩
      · simp [v₄,v₃,v₂,inc,addr,addi,Op.eval,ne₁,id₁]
      · simp [v₄,v₃,v₂,inc,addr,addi,Op.eval,ne₂,ne₃,li₁]
      · rw [show part (i+1)=part i+f x (push i ρ) from Finset.sum_range_succ _ _]
        apply Prod.ext
        · simpa [v₄,v₃,v₂,inc,addr,addi,Op.eval,Ne.symm ne₁,zi] using congrArg (fun a:ℤ=>a+(f x (push i ρ)).1) ai
        · simpa [v₄,v₃,v₂,inc,addr,addi,Op.eval,zr] using congrArg (fun a:ℝ=>a+(f x (push i ρ)).2) ar
      · intro j hj
        have nj : j ≠ idx := by dsimp [idx];omega
        obtain ⟨u₁,u₂⟩ := kz.1 j (by dsimp [tmp];omega)
        simpa [v₄,v₃,v₂,inc,addr,addi,Op.eval,nj,ne_of_lt hj,u₁,u₂] using k.1 j hj
  obtain ⟨out,c,ec,tc,last⟩ := BoundedSum.bounded_while_execution x.dist body guard A N _ hl 0 (Nat.zero_le _) u start
  refine ⟨out,_,Executes.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) ec)))),
    last.2.2.2,last.2.2.1,?_⟩
  have le : N ≤ x.cap+1 := by cases a <;> dsimp [N,World.size,World.cap] <;> omega
  have mul := Nat.mul_le_mul_right (p.eval x.cap+5) le
  change c ≤ (N-0)*(p.eval x.cap+5)+2 at tc
  simp only [Nat.sub_zero] at tc
  simp only [eval_add,eval_mul,eval_X,eval_C,eval_one]
  omega
