-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.BoundedSum.bounded_sum_register_engine
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:11:21.77659+00:00
-- url     : https://prove2.me/submissions/83cd4dbe-3443-453b-af2e-6b1d1d437c9f

import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_while_execution
import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
open scoped Classical

theorem solution (f g : Env→ℕ) (hf : Engine f) (hg : Engine g) :
    Engine (fun ρ=>∑ i ∈ Finset.range (f ρ),g (push i ρ)) := by
  classical
  obtain ⟨p,hp⟩ := hf
  obtain ⟨q,hq⟩ := hg
  refine ⟨p+(p+1)*(q.comp (X+p)+C 6)+C 8,?_⟩
  intro src b small
  let lim := b+1
  let idx := b+2
  let temp := b+3
  obtain ⟨boundCode,cb⟩ := hp src lim (fun j=>by dsimp [lim];have:=small j;omega)
  have room (j : ℕ) : push idx src j < temp := by cases j with
    | zero => dsimp [push,idx,temp];omega
    | succ j => dsimp [push,temp];have:=small j;omega
  obtain ⟨term,ct⟩ := hq (push idx src) temp room
  let put := fun (a : ℕ) (z : ℤ)=> Op.pointerConst a z
  let add := Op.pointerAdd b b temp
  let inc := Op.pointerInc idx
  let body := Cmd.seq term (.seq (.atom add) (.atom inc))
  let guard := Cond.pointerLE idx lim
  let loop := Cmd.whileDo guard body
  refine ⟨.seq boundCode (.seq (.atom (put b 0)) (.seq (.atom (put idx 0))
    (.seq (.atom (.pointerDec lim)) loop))),?_⟩
  intro n d s ρ M initBound initRead
  let N := f ρ
  let Q := q.eval (M+p.eval M)
  let partialSum (j : ℕ) := ∑i ∈ Finset.range j,g (push i ρ)
  let A (i : ℕ) (v : Store) := v.ptrs idx=(i:ℤ) ∧ v.ptrs lim=(N:ℤ)-1 ∧
    v.ptrs b=(partialSum i:ℤ) ∧ Keeps b s v ∧ partialSum i ≤ i*Q
  obtain ⟨u,z,eu,ku,vu,zu,nu⟩ := cb n d s ρ M initBound initRead
  let s₁ := (put b 0).eval d u
  let s₂ := (put idx 0).eval d s₁
  let s₃ := (Op.pointerDec lim).eval d s₂
  have start : A 0 s₃ := by
    dsimp only [A]
    refine ⟨?_,?_,?_,⟨?_,ku.2⟩,by simp [partialSum]⟩
    · simp [s₃,s₂,s₁,put,Op.eval,lim,idx]
    · simpa [s₃,s₂,s₁,put,Op.eval,lim,idx,N] using congrArg (fun x : ℤ=>x-1) vu
    · simp [s₃,s₂,s₁,put,Op.eval,lim,idx,partialSum]
    · intro j hj
      simpa [s₃,s₂,s₁,put,Op.eval,lim,idx,show j ≠ b+1 by omega,show j ≠ b+2 by omega,ne_of_lt hj] using ku.1 j (show j < lim by dsimp [lim];omega)
  have hloop : LoopBound d body guard A N (Q+2) := by
    constructor
    · intro i v av
      change v.ptrs idx ≤ v.ptrs lim ↔ i < N
      rw [av.1,av.2.1];omega
    · intro i hi v av
      obtain ⟨vi,vl,vs,kv,psum⟩ := av
      have arg (j : ℕ) : v.ptrs (push idx src j)=(push i ρ j:ℤ) := by
        cases j with
        | zero => exact vi
        | succ j => exact (kv.1 _ (small j)).trans (initRead j)
      have sub (j : ℕ) : push i ρ j ≤ M+p.eval M := by
        cases j with
        | zero => change i ≤ _;dsimp [N] at hi;omega
        | succ j => exact (initBound j).trans (Nat.le_add_right _ _)
      obtain ⟨v₁,zt,et,kt,vt,bt,gt⟩ := ct n d v (push i ρ) _ sub arg
      let v₂ := add.eval d v₁
      let v₃ := inc.eval d v₂
      have ne₁ : idx ≠ b := by dsimp [idx];omega
      have ne₂ : lim ≠ idx := by dsimp [lim,idx];omega
      have ne₃ : lim ≠ b := by dsimp [lim];omega
      have hidx := (kt.1 idx (by dsimp [idx,temp];omega)).trans vi
      have hlim := (kt.1 lim (by dsimp [lim,temp];omega)).trans vl
      have hsum := (kt.1 b (by dsimp [temp];omega)).trans vs
      refine ⟨v₃,_,Executes.seq et (.seq (.atom _ _) (.atom _ _)),by change zt+(1+1) ≤ Q+2;dsimp [Q];omega,?_⟩
      refine ⟨?_,?_,?_,⟨?_,kt.2.trans kv.2⟩,?_⟩
      · simp [v₃,v₂,add,inc,Op.eval,ne₁,hidx]
      · simp [v₃,v₂,add,inc,Op.eval,ne₂,ne₃,hlim]
      · simp [v₃,v₂,add,inc,Op.eval,Ne.symm ne₁,hsum,vt,partialSum,Finset.sum_range_succ]
      · intro j hj
        have jx : j ≠ idx := by dsimp [idx];omega
        simp [v₃,v₂,add,inc,Op.eval,jx,ne_of_lt hj]
        exact (kt.1 j (by dsimp [temp];omega)).trans (kv.1 j hj)
      · change partialSum (i+1) ≤ (i+1)*Q
        rw [show partialSum (i+1)=partialSum i+g (push i ρ) from Finset.sum_range_succ _ _,Nat.succ_mul]
        exact Nat.add_le_add psum gt
  obtain ⟨out,c,ec,clock,atEnd⟩ := bounded_while_execution d body guard A N (Q+2) hloop 0 (Nat.zero_le _) s₃ start
  refine ⟨out,_,Executes.seq eu (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) ec))),
    atEnd.2.2.2.1,atEnd.2.2.1,?_,?_⟩
  · change z+(1+(1+(1+c))) ≤ _
    simp only [eval_add,eval_mul,eval_comp,eval_X,eval_C,eval_one]
    simp only [Nat.sub_zero] at clock
    have h := Nat.mul_le_mul (show N ≤ p.eval M+1 by dsimp [N];omega) (show Q+2+2 ≤ Q+6 by omega)
    dsimp [Q] at *;omega
  · have vv := atEnd.2.2.2.2
    change partialSum N ≤ _
    simp only [eval_add,eval_mul,eval_comp,eval_X,eval_C,eval_one]
    have h := Nat.mul_le_mul (show N ≤ p.eval M+1 by dsimp [N];omega) (show Q ≤ Q+6 by omega)
    dsimp [Q] at *;omega

