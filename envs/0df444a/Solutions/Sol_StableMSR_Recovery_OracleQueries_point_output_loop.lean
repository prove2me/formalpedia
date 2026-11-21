-- Prove2me | solution 1 for StableMSR.Recovery.OracleQueries.point_output_loop
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:30:03.118772+00:00
-- url     : https://prove2.me/submissions/e6815fea-f5c9-4d4e-87dd-dbd091804663

import Theorems.Thm_StableMSR_Recovery_OracleQueries_bounded_oracle_expression_compiler
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

theorem solution (f : World→ℕ→ℤ) (h : Form (fun x ρ=>iv (f x (ρ 0)))) :
    ∃ p : Polynomial ℕ, ∃cmd : Cmd,∀ (x : World) (s : Store),Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z ≤ p.eval x.cap ∧
      ∀i < x.n,t.imem (-1-(i:ℤ))=f x i := by
  classical
  obtain ⟨p,hp⟩ := bounded_oracle_expression_compiler _ h
  obtain ⟨entry,ce⟩ := hp 6 (fun _=>3) (by decide) (fun _=>by decide)
  let ini := Op.pointerConst 3 0
  let dst := Op.pointerConst 4 (-1)
  let cpy := Op.pointerCopy 5 0
  let dec := Op.pointerDec 5
  let wr := Op.integerStore 4 6
  let back := Op.pointerDec 4
  let inc := Op.pointerInc 3
  let body := Cmd.seq entry (.seq (.atom wr) (.seq (.atom back) (.atom inc)))
  let guard := Cond.pointerLE 3 5
  refine ⟨(X+1)*(p+C 5)+C 8,.seq (.atom ini) (.seq (.atom dst) (.seq (.atom cpy) (.seq (.atom dec) (.whileDo guard body)))),?_⟩
  intro x s rs
  let u := dec.eval x.dist (cpy.eval x.dist (dst.eval x.dist (ini.eval x.dist s)))
  let A (i : ℕ) (v : Store) := Ready x v ∧ v.ptrs 3=(i:ℤ) ∧ v.ptrs 4=(-1-(i:ℤ)) ∧
    v.ptrs 5=(x.n:ℤ)-1 ∧ ∀j < i,v.imem (-1-(j:ℤ))=f x j
  have start : A 0 u := by
    dsimp only [A]
    have sz : s.ptrs 0=(x.n:ℤ) := rs.1 .points
    refine ⟨⟨?_,rs.2⟩,?_,?_,?_,by simp⟩
    · intro a;have use := rs.1 a;cases a <;> simpa [u,dec,cpy,dst,ini,Op.eval,Axis.reg,Function.update] using use
    all_goals simp [u,dec,cpy,dst,ini,Op.eval,Function.update,sz]
  have loop : BoundedSum.LoopBound x.dist body guard A x.n (p.eval x.cap+3) := by
    constructor
    · intro i v av
      change v.ptrs 3 ≤ v.ptrs 5 ↔ i < x.n
      rw [av.2.1,av.2.2.2.1];omega
    · intro i hi v av
      obtain ⟨ready,pi,pa,pl,prev⟩ := av
      obtain ⟨v₁,z,ez,keep,vz,tz⟩ := ce x v (fun _=>i) ready (fun _=>pi)
      have val : v₁.ptrs 6=f x i := congrArg Prod.fst vz
      have a3 := (keep.1 3 (by decide)).1.trans pi
      have a4 := (keep.1 4 (by decide)).1.trans pa
      have a5 := (keep.1 5 (by decide)).1.trans pl
      let v₂ := wr.eval x.dist v₁
      let v₃ := back.eval x.dist v₂
      let v₄ := inc.eval x.dist v₃
      refine ⟨v₄,_,Executes.seq ez (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))),by omega,⟨?_,?_⟩,?_,?_,?_,?_⟩
      · intro a
        have h := (keep.1 a.reg (by have:=axSmall a;omega)).1.trans (ready.1 a)
        have n3 : a.reg ≠ 3 := ne_of_lt (axSmall a)
        have n4 : a.reg ≠ 4 := by have:=axSmall a;omega
        simpa [v₄,v₃,v₂,inc,back,wr,Op.eval,n3,n4] using h
      · intro j
        have ne : (j:ℤ) ≠ -1-(i:ℤ) := by omega
        simpa [v₄,v₃,v₂,inc,back,wr,Op.eval,a4,Function.update_of_ne ne,keep.2] using ready.2 j
      · simp [v₄,v₃,v₂,inc,back,wr,Op.eval,Function.update,a3]
      · simp [v₄,v₃,v₂,inc,back,wr,Op.eval,Function.update,a4];omega
      · simp [v₄,v₃,v₂,inc,back,wr,Op.eval,Function.update,a5]
      · intro j hj
        by_cases eq : j=i
        · subst j;simp [v₄,v₃,v₂,inc,back,wr,Op.eval,a4,val]
        · have ne : -1-(j:ℤ) ≠ -1-(i:ℤ) := by omega
          simpa [v₄,v₃,v₂,inc,back,wr,Op.eval,a4,Function.update_of_ne ne,keep.2] using prev j (by omega)
  obtain ⟨out,z,ez,tz,last⟩ := BoundedSum.bounded_while_execution x.dist body guard A x.n _ loop 0 (Nat.zero_le _) u start
  refine ⟨out,_,Executes.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) ez))),?_,last.2.2.2.2⟩
  have mul := Nat.mul_le_mul_right (p.eval x.cap+5) (show x.n ≤ x.cap+1 by unfold World.cap;omega)
  change z ≤ (x.n-0)*(p.eval x.cap+5)+2 at tz
  simp only [Nat.sub_zero] at tz
  simp only [eval_add,eval_mul,eval_X,eval_C,eval_one]
  omega
