-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.BoundedSum.bounded_stream_writer
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:10:36.996121+00:00
-- url     : https://prove2.me/submissions/cf95cf9d-c324-43da-a976-2a1c0f7164c8

import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_sum_compiler
import Theorems.Thm_StableMSR_Recovery_Compiler_compiler_execution_exact
import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_while_execution
import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
set_option maxHeartbeats 1600000
open scoped Classical
private lemma monomial_bound (p : Polynomial ℕ) :
    ∃ a b : ℕ,0 < a ∧ 0 < b ∧ ∀m : ℕ,1 ≤ m → p.eval m ≤ a*m^b := by
  classical
  let e := p.natDegree+1
  let s := ∑ i ∈ Finset.range e,p.coeff i
  refine ⟨s+1,e,by omega,Nat.succ_pos _,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ Finset.range e,p.coeff i*m^e := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Nat.le_of_lt (Finset.mem_range.mp hi)))
    _ = s*m^e := (Finset.sum_mul ..).symm
    _ ≤ (s+1)*m^e := Nat.mul_le_mul_right _ (by omega)

theorem solution (len : ℕ→ℕ) (value : ℕ→ℕ→ℕ) (hl : Form (fun ρ=>len (ρ 0)))
    (hv : Form (fun ρ=>value (ρ 0) (ρ 1))) :
    ∃ a b : ℕ,0 < a ∧ 0 < b ∧ ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
    ∀m : ℕ,1 ≤ m → ∃t ≤ a*m^b,
      let s := execute P m 0 (fun _ _=>0) t
      s.halted=true ∧ s.work ≤ a*m^b ∧ len m ≤ a*m^b ∧
      ∀j < len m,s.imem (-1-(j:ℤ))=(value m j:ℤ) := by
  classical
  obtain ⟨p,hp⟩ := bounded_sum_compiler _ hl
  obtain ⟨q,hq⟩ := bounded_sum_compiler _ hv
  let src (i : ℕ) := if i=0 then 0 else if i=1 then 1 else 2
  obtain ⟨lengthCmd,cl⟩ := hp src 3 (fun i=>by simp only [src];split <;> (try split) <;> decide)
  obtain ⟨entry,ce⟩ := hq src 5 (fun i=>by simp only [src];split <;> (try split) <;> decide)
  let load := Op.integerLoad 0 0
  let put := Op.pointerConst 4 (-1)
  let dec := Op.pointerDec 3
  let write := Op.integerStore 4 5
  let back := Op.pointerDec 4
  let inc := Op.pointerInc 1
  let body := Cmd.seq entry (.seq (.atom write) (.seq (.atom back) (.atom inc)))
  let guard := Cond.pointerLE 1 3
  let cmd := Cmd.seq (.atom load) (.seq lengthCmd (.seq (.atom put) (.seq (.atom dec) (.whileDo guard body))))
  let poly : Polynomial ℕ := p+(p+1)*(q.comp (X+p)+C 6)+C 10
  obtain ⟨a,b,ha,hb,mono⟩ := monomial_bound poly
  obtain ⟨hd,correct⟩ := compiler_execution_exact cmd 0
  refine ⟨a,b,ha,hb,compile cmd 0,hd,?_⟩
  intro m hm
  let d : Point m→Point m→ℝ := fun _ _=>0
  let s := initialStore m 0
  let u := load.eval d s
  have input (i : ℕ) : u.ptrs (src i)=(inputEnv m 0 i:ℤ) := by
    by_cases h : i=0
    · subst i;simp [u,load,s,Op.eval,initialStore,src,inputEnv]
    · by_cases h' : i=1 <;> simp [h,h',u,load,s,Op.eval,initialStore,src,inputEnv]
  have size (i : ℕ) : inputEnv m 0 i ≤ m := by simp [inputEnv];split <;> omega
  obtain ⟨u₁,z,ez,kz,valz,tz,lz⟩ := cl m d u (inputEnv m 0) m size input
  change u₁.ptrs 3=(len m:ℤ) at valz
  change len m ≤ p.eval m at lz
  let u₂ := put.eval d u₁
  let u₃ := dec.eval d u₂
  let Q := q.eval (m+p.eval m)
  let A (i : ℕ) (v : Store) := v.ptrs 0=(m:ℤ) ∧ v.ptrs 1=(i:ℤ) ∧ v.ptrs 2=0 ∧
    v.ptrs 3=(len m:ℤ)-1 ∧ v.ptrs 4=(-1-(i:ℤ)) ∧
    ∀j < i,v.imem (-1-(j:ℤ))=(value m j:ℤ)
  have start : A 0 u₃ := by
    dsimp only [A]
    have p0 := kz.1 0 (by decide)
    have p1 := kz.1 1 (by decide)
    have p2 := kz.1 2 (by decide)
    simp [u₃,u₂,put,dec,Op.eval,p0,p1,p2,u,load,s,initialStore,valz,Function.update]
  have loop : LoopBound d body guard A (len m) (Q+3) := by
    constructor
    · intro i v av
      change v.ptrs 1 ≤ v.ptrs 3 ↔ i < len m
      rw [av.2.1,av.2.2.2.1];omega
    · intro i hi v av
      obtain ⟨p0,p1,p2,p3,p4,prev⟩ := av
      have arg (j : ℕ) : v.ptrs (src j)=(inputEnv m i j:ℤ) := by
        by_cases h : j=0
        · simp [src,inputEnv,h,p0]
        · by_cases g : j=1 <;> simp [h,g,src,inputEnv,p1,p2]
      have small (j : ℕ) : inputEnv m i j ≤ m+p.eval m := by
        simp only [inputEnv];split <;> (try split) <;> omega
      obtain ⟨v₁,k,ek,keep,vk,tk,_⟩ := ce m d v (inputEnv m i) _ small arg
      change v₁.ptrs 5=(value m i:ℤ) at vk
      have a0 := (keep.1 0 (by decide)).trans p0
      have a1 := (keep.1 1 (by decide)).trans p1
      have a2 := (keep.1 2 (by decide)).trans p2
      have a3 := (keep.1 3 (by decide)).trans p3
      have a4 := (keep.1 4 (by decide)).trans p4
      let v₂ := write.eval d v₁
      let v₃ := back.eval d v₂
      let v₄ := inc.eval d v₃
      refine ⟨v₄,_,Executes.seq ek (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))),
        by change k+(1+(1+1)) ≤ Q+3;dsimp [Q];omega,?_⟩
      dsimp only [A]
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · simp [v₄,v₃,v₂,inc,back,write,Op.eval,Function.update,a0]
      · simp [v₄,v₃,v₂,inc,back,write,Op.eval,Function.update,a1]
      · simp [v₄,v₃,v₂,inc,back,write,Op.eval,Function.update,a2]
      · simp [v₄,v₃,v₂,inc,back,write,Op.eval,Function.update,a3]
      · simp [v₄,v₃,v₂,inc,back,write,Op.eval,Function.update,a4];omega
      · intro j hj
        by_cases same : j=i
        · subst j;simp [v₄,v₃,v₂,inc,back,write,Op.eval,a4,vk]
        · have ne : (-1-(j:ℤ)) ≠ (-1-(i:ℤ)) := by omega
          simpa [v₄,v₃,v₂,inc,back,write,Op.eval,a4,Function.update_of_ne ne,keep.2] using prev j (by omega)
  obtain ⟨out,c,ec,clock,last⟩ := bounded_while_execution d body guard A (len m) (Q+3) loop 0 (Nat.zero_le _) u₃ start
  let steps := 1+(z+(1+(1+c)))
  have exec : Executes d cmd s out steps := .seq (.atom _ _) (.seq ez (.seq (.atom _ _) (.seq (.atom _ _) ec)))
  have eq : execute (compile cmd 0) m 0 d (steps+1)=out.haltedState cmd.size (0+steps+1) 0 := by
    have init : MinSumFPT.initState m 0 0 0=s.state 0 0 := by
      simp [s,initialStore,Store.state,MinSumFPT.initState]
    unfold execute MinSumFPT.run
    rw [init]
    exact correct m d s out steps exec (fun _=>0) 0
  have bound : steps+1 ≤ poly.eval m := by
    simp only [Nat.sub_zero] at clock
    simp only [poly,eval_add,eval_mul,eval_comp,eval_X,eval_C,eval_one]
    have h := Nat.mul_le_mul (show len m ≤ p.eval m+1 by omega) (show Q+3+2 ≤ Q+6 by omega)
    dsimp [Q,steps] at *;omega
  have lenBound : len m ≤ poly.eval m := by
    simp only [poly,eval_add,eval_mul,eval_comp,eval_X,eval_C,eval_one];omega
  have total := bound.trans (mono m hm)
  refine ⟨steps+1,total,?_⟩
  change (execute (compile cmd 0) m 0 d (steps+1)).halted=true ∧ _
  rw [eq]
  exact ⟨rfl,by simpa [Store.haltedState,Store.state] using total,lenBound.trans (mono m hm),last.2.2.2.2.2⟩

