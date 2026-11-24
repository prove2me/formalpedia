-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.native_slot_classification
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:23:39.66591+00:00
-- url     : https://prove2.me/submissions/cbd8b6e1-da7d-425e-b43c-3d2fc7e86538

import Definitions.Def_StableMSR_RegionalProductionTable
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
namespace StableMSR.Recovery.NativeWriter.Relative.Machine
open Compiler
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 14000
def line : List Op → Cmd | []=>.skip | o::os=>.seq (.atom o) (line os)
noncomputable def perform {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) : List Op → Store
  | []=>s | o::os=>perform d (o.eval d s) os
theorem line_exec {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (os : List Op) :
    Executes d (line os) s (perform d s os) os.length := by
  induction os generalizing s with
  | nil=>exact .skip _
  | cons o os ih=>simpa only [line,perform,List.length_cons,Nat.add_comm 1] using Executes.seq (.atom o s) (ih (o.eval d s))

end StableMSR.Recovery.NativeWriter.Relative.Machine
namespace StableMSR.Recovery.NativeWriter.Production.RAM
open Compiler OracleQueries Relative.Machine
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

abbrev Reg := Fin 32
abbrev Var := Fin 12
def dest (v : Var) : Reg := ⟨16+v.val,by omega⟩
structure Model where
  reg : Reg→ℤ
  mem : ℤ→ℤ
def Model.set (s : Model) (v : Var) (z : ℤ) : Model := {s with reg:=Function.update s.reg (dest v) z}
def Model.put (s : Model) (a z : ℤ) : Model := {s with mem:=Function.update s.mem a z}
def model (s : Store) : Model := ⟨fun r=>s.ptrs r.val,s.imem⟩
def Match (b : ℕ) (s t : Store) (m : Model) :=
  model t=m ∧ ∀r,32≤r → r<b → t.ptrs r=s.ptrs r

inductive E where
  | lit (k : ℤ)
  | reg (r : Reg)
  | read (a : E)
  | bin (minus : Bool) (a b : E)
def E.val (s : Model) : E→ℤ
  | .lit k=>k | .reg r=>s.reg r | .read a=>s.mem (a.val s)
  | .bin b x y=>if b then x.val s-y.val s else x.val s+y.val s
def E.code : E→ℕ→Cmd
  | .lit z,b=>.atom (.pointerConst b z)
  | .reg r,b=>.atom (.pointerCopy b r.val)
  | .read a,b=>.seq (a.code b) (.atom (.integerLoad b b))
  | .bin sub a c,b=>.seq (a.code b) (.seq (c.code (b+1)) (.atom (if sub then .pointerSub b b (b+1) else .pointerAdd b b (b+1))))
def E.cost : E→ℕ
  | .lit _ | .reg _=>1 | .read a=>a.cost+1 | .bin _ a b=>a.cost+(b.cost+1)

def Quiet (b : ℕ) (s t : Store) := (∀r<b,t.ptrs r=s.ptrs r) ∧ t.imem=s.imem
theorem model_eq {s t : Store} {b : ℕ} (hb:32≤b) (h : Quiet b s t) : model t=model s := by
  exact congrArg₂ Model.mk (funext (fun r=>h.1 r.val (by omega))) h.2

theorem expr_run {n : ℕ} (d : Point n→Point n→ℝ) (e : E) (s : Store) (b : ℕ) (hb : 32≤b) :
    ∃t,Executes d (e.code b) s t e.cost ∧ Quiet b s t ∧ t.ptrs b=e.val (model s) := by
  induction e generalizing b s with
  | lit z=>
    exact ⟨_,.atom _ _,⟨fun r hr=>Function.update_of_ne (by omega) ..,rfl⟩,Function.update_self ..⟩
  | reg j=>
    exact ⟨_,.atom _ _,⟨fun r hr=>Function.update_of_ne (by omega) ..,rfl⟩,Function.update_self ..⟩
  | read a ih=>
    obtain ⟨t,ex,fr,v⟩:=ih s b hb
    refine ⟨_,.seq ex (.atom (.integerLoad b b) _),⟨?_,fr.2⟩,?_⟩
    · intro r hr;exact (Function.update_of_ne (by omega:r≠b) ..).trans (fr.1 r hr)
    · simp [Op.eval,E.val,v,fr.2,model]
  | bin sub a c ia ic=>
    obtain ⟨t,ex,fr,v⟩:=ia s b hb
    obtain ⟨u,ey,fr',w⟩:=ic t (b+1) (by omega)
    have vx:u.ptrs b=a.val (model s):=(fr'.1 _ (by omega)).trans v
    rw [model_eq hb fr] at w
    cases sub <;> refine ⟨_,.seq ex (.seq ey (.atom _ _)),⟨?_,fr'.2.trans fr.2⟩,?_⟩
    all_goals first | (intro r hr;exact (Function.update_of_ne (by omega:r≠b) ..).trans ((fr'.1 _ (by omega)).trans (fr.1 _ hr)))
                    | simp [Op.eval,E.val,vx,w]

inductive Axis where | points | events
def Axis.reg : Axis→Reg | .points=>0 | .events=>15
def Axis.len (n T : ℕ) : Axis→ℕ | .points=>n | .events=>T
inductive P where
  | nil
  | set (v : Var) (e : E)
  | put (a e : E)
  | seq (a b : P)
  | test (a b : E) (yes no : P)
  | rep (axis : Axis) (body : P)

def P.run (n T : ℕ) : P→Model→Model
  | .nil,s=>s
  | .set v e,s=>s.set v (e.val s)
  | .put a e,s=>s.put (a.val s) (e.val s)
  | .seq a b,s=>b.run n T (a.run n T s)
  | .test a b yes no,s=>if a.val s≤b.val s then yes.run n T s else no.run n T s
  | .rep ax body,s=>(body.run n T)^[ax.len n T] s

def P.time (n T : ℕ) : P→ℕ
  | .nil=>0 | .set _ e=>e.cost+1 | .put a e=>a.cost+(e.cost+1)
  | .seq a b=>a.time n T+b.time n T
  | .test a b yes no=>a.cost+b.cost+2+max (yes.time n T) (no.time n T)
  | .rep ax body=>4+(ax.len n T)*(3+body.time n T)

def P.code : P→ℕ→Cmd
  | .nil,_=>.skip
  | .set v e,b=>.seq (e.code b) (.atom (.pointerCopy (dest v).val b))
  | .put a e,b=>.seq (a.code b) (.seq (e.code (b+1)) (.atom (.integerStore b (b+1))))
  | .seq a c,b=>.seq (a.code b) (c.code b)
  | .test a c yes no,b=>.seq (a.code b) (.seq (c.code (b+1)) (.ite (.pointerLE b (b+1)) (yes.code b) (no.code b)))
  | .rep ax p,b=>.seq (line [.pointerCopy b ax.reg.val,.pointerConst (b+1) 1])
    (.whileDo (.pointerLE (b+1) b) (.seq (p.code (b+2)) (.atom (.pointerDec b))))
end StableMSR.Recovery.NativeWriter.Production.RAM
namespace StableMSR.Recovery.NativeWriter.Production.RAM
open Compiler OracleQueries Relative.Machine
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

theorem P.fixed (p : P) (n T : ℕ) (m : Model) (r : Reg) (hr : r.val<16) : (p.run n T m).reg r=m.reg r := by
  induction p generalizing m with
  | nil=>rfl
  | put=>rfl
  | set v e=>exact Function.update_of_ne (fun h=>by have z:=congrArg Fin.val h;dsimp [dest] at z;omega) ..
  | seq a b ia ib=>exact (ib _).trans (ia _)
  | test a b l k il ik=>unfold P.run;split <;> first | apply il | apply ik
  | rep ax p ih=>
    change ((p.run n T)^[ax.len n T] m).reg r=_
    induction ax.len n T with
    | zero=>rfl
    | succ a hk=>rw [Function.iterate_succ_apply',ih,hk]

def Fit (n T : ℕ) (s : Store) := s.ptrs 0=(n:ℤ) ∧ s.ptrs 15=(T:ℤ)
theorem fit_after {n T b : ℕ} {p : P} {s t : Store}
    (h : Match b s t (p.run n T (model s))) (ok : Fit n T s) : Fit n T t := by
  have reg (r : Reg) (hr : r.val<16) : t.ptrs r.val=s.ptrs r.val :=
    (congrArg (fun m:Model=>m.reg r) h.1).trans (p.fixed n T _ r hr)
  exact ⟨(reg 0 (by decide)).trans ok.1,(reg 15 (by decide)).trans ok.2⟩

theorem reg_copy (s : Store) {v : Var} (b : ℕ) {n : ℕ} (d : Point n→Point n→ℝ) :
  model ((Op.pointerCopy (dest v).val b).eval d s)=(model s).set v (s.ptrs b) := by
  apply congrArg₂ Model.mk _ rfl
  funext r
  by_cases eq:r=dest v
  · subst r;simp [model,Model.set,Op.eval]
  · have ne:r.val≠(dest v).val:=fun h=>eq (Fin.ext h)
    simp [model,Model.set,Op.eval,Function.update_of_ne eq,Function.update_of_ne ne]

theorem fixed_match {s t : Store} {b : ℕ} (fr : Quiet b s t) (hb:32≤b) : Match b s t (model s) :=
  ⟨model_eq hb fr,fun i _ hi=>fr.1 i hi⟩

theorem execute {n : ℕ} (d : Point n→Point n→ℝ) (T : ℕ) (p : P) (b : ℕ) (hb : 32≤b)
    (s : Store) (fit : Fit n T s) :
    ∃t z,Executes d (p.code b) s t z ∧ z≤p.time n T ∧ Match b s t (p.run n T (model s)) := by
  induction p generalizing b s with
  | nil=>exact ⟨s,0,.skip _,by rfl,⟨rfl,fun _ _ _=>rfl⟩⟩
  | set v e=>
    obtain ⟨t,go,fr,val⟩:=expr_run d e s b hb
    refine ⟨_,_,.seq go (.atom (.pointerCopy (dest v).val b) _),by rfl,?_,?_⟩
    · rw [reg_copy, val,model_eq hb fr];rfl
    · intro i low hi
      change Function.update t.ptrs (dest v).val (t.ptrs b) i=_
      rw [Function.update_of_ne (show i≠(dest v).val by dsimp [dest];omega)]
      exact fr.1 i hi
  | put a e=>
    obtain ⟨t,g1,fr1,v1⟩:=expr_run d a s b hb
    obtain ⟨u,g2,fr2,v2⟩:=expr_run d e t (b+1) (by omega)
    have h:=model_eq hb fr1
    have h':=model_eq (show 32≤b+1 by omega) fr2
    refine ⟨_,_,.seq g1 (.seq g2 (.atom (.integerStore b (b+1)) _)),by rfl,?_,?_⟩
    · have hh:model u=model s:=h'.trans h
      change Model.mk (model u).reg (Function.update (model u).mem (u.ptrs b) (u.ptrs (b+1)))=_
      rw [hh,(fr2.1 b (by omega)).trans v1,v2,h];rfl
    · intro i low hi;exact (fr2.1 _ (by omega)).trans (fr1.1 _ hi)
  | seq p q ip iq=>
    obtain ⟨t,z,g1,c1,m1⟩:=ip b hb s fit
    obtain ⟨u,y,g2,c2,m2⟩:=iq b hb t (fit_after m1 fit)
    exact ⟨u,z+y,.seq g1 g2,Nat.add_le_add c1 c2,⟨m2.1.trans (congrArg _ m1.1),
      fun i lo hi=>(m2.2 i lo hi).trans (m1.2 i lo hi)⟩⟩
  | test a c yes no iy ino=>
    obtain ⟨t,g1,fr1,v1⟩:=expr_run d a s b hb
    obtain ⟨u,g2,fr2,v2⟩:=expr_run d c t (b+1) (by omega)
    have m : model u=model s := (model_eq (by omega:32≤b+1) fr2).trans (model_eq hb fr1)
    have same (i : ℕ) (hi:i<b) : u.ptrs i=s.ptrs i:=(fr2.1 _ (by omega)).trans (fr1.1 _ hi)
    have fu:Fit n T u:=⟨(same 0 (by omega)).trans fit.1,(same 15 (by omega)).trans fit.2⟩
    have cond : (Cond.pointerLE b (b+1)).test u ↔ a.val (model s)≤c.val (model s) := by
      change u.ptrs b≤u.ptrs (b+1) ↔ _;rw [(fr2.1 b (by omega)).trans v1,v2,model_eq hb fr1]
    by_cases h:a.val (model s)≤c.val (model s)
    · obtain ⟨v,z,go,cost,mt⟩:=iy b hb u fu
      exact ⟨v,_,.seq g1 (.seq g2 (.ite_true (cond.mpr h) go)),by dsimp [P.time];omega,
        ⟨by simpa only [P.run,if_pos h,m] using mt.1,fun i lo hi=>(mt.2 i lo hi).trans (same i hi)⟩⟩
    · obtain ⟨v,z,go,cost,mt⟩:=ino b hb u fu
      exact ⟨v,_,.seq g1 (.seq g2 (.ite_false (fun z=>h (cond.mp z)) go)),by dsimp [P.time];omega,
        ⟨by simpa only [P.run,if_neg h,m] using mt.1,fun i lo hi=>(mt.2 i lo hi).trans (same i hi)⟩⟩
  | rep ax p ih=>
    let ops : List Op:=[.pointerCopy b ax.reg.val,.pointerConst (b+1) 1]
    let a:=perform d s ops
    have base:Quiet b s a:=by
      refine ⟨?_,rfl⟩;intro j hj
      simp [a,ops,perform,Op.eval,Function.update_of_ne (by omega:j≠b),Function.update_of_ne (by omega:j≠b+1)]
    have cnt:a.ptrs b=(ax.len n T:ℤ):=by
      have v:s.ptrs ax.reg.val=(ax.len n T:ℤ):=by cases ax <;> first | exact fit.1 | exact fit.2
      simpa [a,ops,perform,Op.eval] using v
    have one:a.ptrs (b+1)=1:=by simp [a,ops,perform,Op.eval]
    let body:=Cmd.seq (p.code (b+2)) (.atom (.pointerDec b))
    have loop (k : ℕ) (a : Store) (fa:Fit n T a) (cnt:a.ptrs b=(k:ℤ)) (one:a.ptrs (b+1)=1) :
        ∃t z,Executes d (.whileDo (.pointerLE (b+1) b) body) a t z ∧ z≤2+k*(3+p.time n T) ∧
          Match b a t ((p.run n T)^[k] (model a)) := by
      induction k generalizing a with
      | zero=>
        exact ⟨a,2,.while_false (by change ¬a.ptrs (b+1)≤a.ptrs b;rw [cnt,one];decide),by simp,⟨rfl,fun _ _ _=>rfl⟩⟩
      | succ k ik=>
        obtain ⟨u,z,go,cost,mt⟩:=ih (b+2) (by omega) a fa
        let v:=(Op.pointerDec b).eval d u
        have low : Quiet b u v:=⟨fun r hr=>Function.update_of_ne (by omega) ..,rfl⟩
        have mc:model v=model u:=model_eq hb low
        have fu:=fit_after mt fa
        have fv:Fit n T v:=⟨(low.1 _ (by omega)).trans fu.1,(low.1 _ (by omega)).trans fu.2⟩
        have cv:v.ptrs b=(k:ℤ):=by simp [v,Op.eval,mt.2 b hb (by omega),cnt]
        have ov:v.ptrs (b+1)=1:=by simp [v,Op.eval,mt.2 (b+1) (by omega) (by omega),one]
        obtain ⟨t,y,rest,cy,mm⟩:=ik v fv cv ov
        refine ⟨t,_,.while_true (by change a.ptrs (b+1)≤a.ptrs b;rw [one,cnt];omega) (.seq go (.atom _ _)) rest,?_,?_,?_⟩
        · rw [Nat.succ_mul];omega
        · rw [Function.iterate_succ_apply];exact mm.1.trans (congrArg _ (mc.trans mt.1))
        · intro j lj hj;exact (mm.2 j lj hj).trans ((low.1 j hj).trans (mt.2 j lj (by omega)))
    obtain ⟨t,z,go,cost,mt⟩:=loop (ax.len n T) a ⟨(base.1 _ (by omega)).trans fit.1,(base.1 _ (by omega)).trans fit.2⟩ cnt one
    refine ⟨t,_,.seq (line_exec d s ops) go,?_,⟨mt.1.trans (congrArg _ (model_eq hb base)),
       fun i lo hi=>(mt.2 i lo hi).trans (base.1 i hi)⟩⟩
    · change 2+z≤4+_;omega

end StableMSR.Recovery.NativeWriter.Production.RAM
namespace StableMSR.Recovery.NativeWriter.Production.RAM
open SingleCircuit SingleRAM Relative Relative.Machine Compiler OracleQueries
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000

abbrev gc : Var := 0
abbrev tail : Var := 1
abbrev ix : Var := 2
abbrev refV : Var := 3
abbrev outB : Var := 4
abbrev inB : Var := 5
abbrev bitI : Var := 6
def V (j : Var) := E.reg (dest j)
def plus := E.bin false
def sub := E.bin true
def inc (v : Var) : P := .set v (plus (V v) (.lit 1))
def eight (e : E) := let t:=plus e e;let u:=plus t t;plus u u
def W (lane : ℕ) (i : E) := sub (.lit (-(32+(lane:ℤ)))) (eight i)
def C (lane : ℕ) (i : E) := W 7 (plus (eight i) (.lit (lane:ℤ)))
def wz (lane : ℕ) (z : ℤ) := -(32+8*z+(lane:ℤ))
def cz (lane : ℕ) (z : ℤ) := wz 7 (8*z+(lane:ℤ))
@[simp] theorem eight_val (m : Model) (e : E) : (eight e).val m=8*e.val m := by simp [eight,plus,E.val];ring
@[simp] theorem W_val (m : Model) (a : ℕ) (e : E) : (W a e).val m=wz a (e.val m) := by simp [W,sub,E.val,wz];ring
@[simp] theorem C_val (m : Model) (a : ℕ) (e : E) : (C a e).val m=cz a (e.val m) := by simp [C,cz,plus,E.val]
@[simp] theorem wz_nat (a i : ℕ) : wz a (i:ℤ)=word a i:=rfl
@[simp] theorem cz_nat (a i : ℕ) : cz a (i:ℤ)=cell a i:=by simp [cz,cell,word,wz]
@[simp] theorem V_val (m : Model) (v : Var) : (V v).val m=m.reg (dest v):=rfl
@[simp] theorem plus_val (m : Model) (a b : E) : (plus a b).val m=a.val m+b.val m:=rfl
@[simp] theorem sub_val (m : Model) (a b : E) : (sub a b).val m=a.val m-b.val m:=rfl
@[simp] theorem lit_val (m : Model) (z : ℤ) : (E.lit z).val m=z:=rfl
@[simp] theorem reg_val (m : Model) (r : Reg) : (E.reg r).val m=m.reg r:=rfl
@[simp] theorem read_val (m : Model) (a : E) : (E.read a).val m=m.mem (a.val m):=rfl
@[simp] theorem set_mem (m : Model) (v : Var) (z : ℤ) : (m.set v z).mem=m.mem:=rfl
@[simp] theorem put_reg (m : Model) (q z : ℤ) : (m.put q z).reg=m.reg:=rfl
@[simp] theorem set_reg (m : Model) (v : Var) (z : ℤ) (r : Reg) :
    (m.set v z).reg r=if r=dest v then z else m.reg r := Function.update_apply ..
@[simp] theorem put_mem (m : Model) (a z q : ℤ) :
    (m.put a z).mem q=if q=a then z else m.mem q := Function.update_apply ..
def seqs : List P→P | []=>.nil | p::ps=>.seq p (seqs ps)
end StableMSR.Recovery.NativeWriter.Production.RAM
namespace StableMSR.Recovery.NativeWriter.Production.RAM
open Compiler OracleQueries
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

def P.allowed : P→Bool→Bool→Bool
  | .nil,_,_ | .set _ _,_,_ | .put _ _,_,_=>true
  | .seq a b,u,v | .test _ _ a b,u,v=>a.allowed u v && b.allowed u v
  | .rep .points b,u,v=>u && b.allowed false v
  | .rep .events b,u,v=>v && b.allowed u false

def P.weight : P→ℕ
  | .nil=>0 | .set _ e=>e.cost+1 | .put a e=>a.cost+(e.cost+1)
  | .seq a b=>a.weight+b.weight | .test a b p q=>a.cost+b.cost+2+(p.weight+q.weight)
  | .rep _ b=>7+b.weight

def fac (n T : ℕ) (u v:Bool) := (if u then 1+n else 1)*(if v then 1+T else 1)
theorem fac_ge (n T : ℕ) (u v:Bool) : 1≤fac n T u v:=by cases u <;> cases v <;> simp [fac] <;> nlinarith
theorem repeat_bound (z b L F : ℕ) (hf : 1≤F) (h:z≤b*F) :
    4+L*(3+z)≤(7+b)*((1+L)*F) := by
  calc 4+L*(3+z) ≤ 4+L*(3+b*F) := by gcongr
       _ ≤ (7+b)*((1+L)*F) := by nlinarith [Nat.mul_le_mul_left L hf,Nat.zero_le (b*F),Nat.zero_le L]

theorem time_bound (p : P) (n T : ℕ) (u v:Bool) (ok:p.allowed u v=true) :
    p.time n T≤p.weight*fac n T u v := by
  have hf:=fac_ge n T u v
  induction p generalizing u v with
  | nil=>simp [P.time,P.weight]
  | set _ e=>exact Nat.le_mul_of_pos_right _ hf
  | put a e=>exact Nat.le_mul_of_pos_right _ hf
  | seq a b ia ib=>
    obtain ⟨x,y⟩:=(by simpa only [P.allowed,Bool.and_eq_true] using ok : _ ∧ _)
    simpa [P.time,P.weight,Nat.add_mul] using Nat.add_le_add (ia u v x hf) (ib u v y hf)
  | test a b l r il ir=>
    obtain ⟨x,y⟩:=(by simpa only [P.allowed,Bool.and_eq_true] using ok : _ ∧ _)
    have h₁:=il u v x hf;have h₂:=ir u v y hf
    have cap:=Nat.le_mul_of_pos_right (a.cost+b.cost+2) hf
    simp only [P.time,P.weight,Nat.add_mul]
    simp only [Nat.add_mul] at cap
    omega
  | rep ax b ih=>
    cases ax with
    | points=>
      obtain ⟨u,ok⟩:=(by simpa only [P.allowed,Bool.and_eq_true] using ok : _ ∧ _);subst u
      have z:=repeat_bound _ _ n _ (fac_ge n T false v) (ih false v ok (fac_ge n T _ _))
      simpa [P.time,P.weight,Axis.len,fac] using z
    | events=>
      obtain ⟨v,ok⟩:=(by simpa only [P.allowed,Bool.and_eq_true] using ok : _ ∧ _);subst v
      have z:=repeat_bound _ _ T _ (fac_ge n T u false) (ih u false ok (fac_ge n T _ _))
      simpa [P.time,P.weight,Axis.len,fac,Nat.mul_comm] using z

end StableMSR.Recovery.NativeWriter.Production.RAM
namespace StableMSR.Recovery.NativeWriter.Production.Classify
open Compiler OracleQueries WindowCSP WindowProfiles RAM Relative.Machine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 14000
set_option maxHeartbeats 1400000

def rawLabel (x : World) (u i:ℕ) := x.mem (sceneBase x u+2+i)
theorem key_iff (x:World) (u:ℕ) (i:Fin x.n) :
    i.val∈keys x u ↔ ¬∃j < i.val,rawLabel x u j=rawLabel x u i.val := by
  have resident (a:Fin x.n) : rep x u a ∈ fibre x u a := Finset.min'_mem _ _
  have labelRep (a:Fin x.n) : rawLabel x u (rep x u a).val=rawLabel x u a.val :=
    (Finset.mem_filter.mp (resident a)).2
  have least (a b:Fin x.n) (h:rawLabel x u b.val=rawLabel x u a.val) : rep x u a≤b :=
    Finset.min'_le (fibre x u a) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  constructor
  · intro h
    obtain ⟨a,_,eq⟩:=Finset.mem_image.mp h
    rintro ⟨j,hj,h⟩
    let b:Fin x.n:=⟨j,by omega⟩
    have ha:rawLabel x u i.val=rawLabel x u a.val:=eq ▸ labelRep a
    have le:(rep x u a).val≤j:=least a b (h.trans ha)
    omega
  · intro h
    have le:(rep x u i).val ≤ i.val:=least i i rfl
    have eq:(rep x u i).val=i.val:=by
      by_contra ne;exact h ⟨_,by omega,labelRep i⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,eq⟩

def baseZ (n u:ℕ) := 3+u*(n+2)
def rowStep := P.test (.reg 0) (V gc)
  (P.seq (.set gc (sub (V gc) (.reg 0))) (.set tail (plus (V tail) (plus (.reg 0) (.lit 2))))) .nil
def coordinates := seqs [.set gc (.reg 3),.set tail (.lit 3),.rep .events rowStep]

theorem row_consume (n T q u i : ℕ) (m:Model) (np:m.reg 0=(n:ℤ))
    (rem:(V gc).val m=((q*n+i:ℕ):ℤ)) (base:(V tail).val m=((baseZ n u:ℕ):ℤ)) :
    let t:=(rowStep.run n T)^[q] m
    (V gc).val t=(i:ℤ) ∧ (V tail).val t=((baseZ n (u+q):ℕ):ℤ) ∧ t.mem=m.mem := by
  induction q generalizing m u with
  | zero=>exact ⟨by simpa using rem,by simpa using base,rfl⟩
  | succ q ih=>
    have ge:m.reg 0≤(V gc).val m:=by rw [np,rem];exact_mod_cast (by rw [Nat.succ_mul];omega : n≤(q+1)*n+i)
    change m.reg 0 ≤ m.reg (dest gc) at ge
    let t:=(m.set gc (m.reg (dest gc)-m.reg 0)).set tail (m.reg (dest tail)+(m.reg 0+2))
    have eq:rowStep.run n T m=t:=by
      simp only [rowStep,P.run,reg_val,if_pos ge,sub_val,plus_val,V_val,lit_val,set_reg,
        show dest tail≠dest gc by decide,show (0:Reg)≠dest gc by decide,if_false,t]
    have low:t.reg 0=(n:ℤ):=np
    have rm:(V gc).val t=((q*n+i:ℕ):ℤ):=by
      change m.reg (dest gc)-m.reg 0=_;change m.reg (dest gc)=_ at rem
      rw [rem,np];push_cast;ring
    have bu:(V tail).val t=((baseZ n (u+1):ℕ):ℤ):=by
      change m.reg (dest tail)+(m.reg 0+2)=_;change m.reg (dest tail)=_ at base
      rw [base,np];simp [baseZ];ring
    rw [Function.iterate_succ_apply,eq]
    simpa only [show u+(q+1)=u+1+q by omega] using (show _ ∧ _ ∧ ((rowStep.run n T)^[q] t).mem=m.mem from ih (u+1) t low rm bu)

theorem coordinate_values (x:World) (m:Model) (r:ℕ) (pn:m.reg 0=(x.n:ℤ)) (slot:m.reg 3=(r:ℤ))
    (hn:0<x.n) (hr:r<x.rows*x.n) :
    let t:=coordinates.run x.n x.rows m
    (V gc).val t=((r%x.n:ℕ):ℤ) ∧ (V tail).val t=((sceneBase x (r/x.n):ℕ):ℤ) ∧ t.mem=m.mem := by
  let q:=r/x.n
  let i:=r%x.n
  have eu:q*x.n+i=r:=by simpa [q,i,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div r x.n
  have room:q≤x.rows:=Nat.le_of_lt ((Nat.div_lt_iff_lt_mul hn).mpr hr)
  have small:i<x.n:=Nat.mod_lt _ hn
  let a:=(m.set gc (m.reg 3)).set tail 3
  have st:(V gc).val a=((q*x.n+i:ℕ):ℤ):=by rw [eu];exact slot
  let t:=(rowStep.run x.n x.rows)^[q] a
  obtain ⟨rem,base,mem⟩:=row_consume x.n x.rows q 0 i a pn st (by simp [a,baseZ])
  have nt:t.reg 0=(x.n:ℤ):=by
    have keep:∀k:ℕ,((rowStep.run x.n x.rows)^[k] a).reg 0=a.reg 0:=by
      intro k;induction k with
      | zero=>rfl
      | succ k ih=>rw [Function.iterate_succ_apply',rowStep.fixed _ _ _ _ (by decide),ih]
    exact (keep q).trans pn
  have below:¬t.reg 0≤(V gc).val t:=by rw [nt,show (V gc).val t=(i:ℤ) from rem];exact_mod_cast (Nat.not_le_of_gt small)
  have still:rowStep.run x.n x.rows t=t:=by
    change (if t.reg 0≤(V gc).val t then _ else t)=t
    rw [if_neg below]
  have same (k:ℕ) : (rowStep.run x.n x.rows)^[k] t=t:=by
    induction k with
    | zero=>rfl
    | succ k ih=>rw [Function.iterate_succ_apply',ih,still]
  change (V gc).val ((rowStep.run x.n x.rows)^[x.rows] a)=_ ∧ _
  have splitRows:(rowStep.run x.n x.rows)^[x.rows] a=t:=by
    calc
      _ = (rowStep.run x.n x.rows)^[x.rows-q+q] a := congrArg (fun N=>(rowStep.run x.n x.rows)^[N] a) (by omega)
      _ = _ := by rw [Function.iterate_add_apply];exact same _
  change (V gc).val ((rowStep.run x.n x.rows)^[x.rows] a)=_ ∧ (V tail).val ((rowStep.run x.n x.rows)^[x.rows] a)=_ ∧ ((rowStep.run x.n x.rows)^[x.rows] a).mem=_
  rw [splitRows]
  exact ⟨rem,by change (V tail).val t=((baseZ x.n q:ℕ):ℤ);simpa only [zero_add] using base,mem⟩

end StableMSR.Recovery.NativeWriter.Production.Classify
namespace StableMSR.Recovery.NativeWriter.Production.Classify
open Compiler OracleQueries WindowCSP WindowProfiles RAM Relative.Machine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

def labelE (j:E) := E.read (plus (plus (V tail) (.lit 2)) j)
def flagStep := P.seq
   (.test (plus (V ix) (.lit 1)) (V gc)
     (.test (labelE (V ix)) (V refV)
        (.test (V refV) (labelE (V ix)) (.set outB (.lit (-1))) .nil) .nil) .nil)
   (inc ix)
def flags := seqs [.set refV (labelE (V gc)),.set ix (.lit 0),.set outB (.lit 0),.rep .points flagStep]
def inspectRows := P.seq coordinates flags

def Duplicate (x:World) (u i k : ℕ) := ∃j<k,j < i ∧ rawLabel x u j=rawLabel x u i
theorem dup_succ (x:World) (u i k:ℕ) : Duplicate x u i (k+1) ↔ Duplicate x u i k ∨ k < i ∧ rawLabel x u k=rawLabel x u i := by
  constructor
  · rintro ⟨j,hj,hi,eq⟩
    by_cases h:j=k
    · exact Or.inr (h ▸ And.intro hi eq)
    · exact Or.inl ⟨j,by omega,hi,eq⟩
  · rintro (⟨j,hj,hi,eq⟩|⟨hi,eq⟩)
    · exact ⟨j,by omega,hi,eq⟩
    · exact ⟨k,by omega,hi,eq⟩

structure Scan (x:World) (u i k : ℕ) (m:Model) : Prop where
  base : (V tail).val m=((sceneBase x u:ℕ):ℤ)
  rem : (V gc).val m=(i:ℤ)
  counter : (V ix).val m=(k:ℤ)
  key : (V refV).val m=rawLabel x u i
  flag : (V outB).val m=if Duplicate x u i k then -1 else 0
  scene : ∀a:ℕ,m.mem a=x.mem a

theorem read_label {x:World} {u:ℕ} {m:Model} (base : (V tail).val m=((sceneBase x u:ℕ):ℤ))
    (scene:∀a:ℕ,m.mem a=x.mem a) (j:E) (k:ℕ) (hk:j.val m=(k:ℤ)) : (labelE j).val m=rawLabel x u k := by
  simp only [labelE,read_val,plus_val,lit_val,base,hk,rawLabel]
  exact_mod_cast scene (sceneBase x u+2+k)

theorem flag_step {x:World} (T u i k:ℕ) (m:Model) (st:Scan x u i k m) :
    let t:=flagStep.run x.n T m
    Scan x u i (k+1) t ∧ t.mem=m.mem := by
  let hit:=k < i ∧ rawLabel x u k=rawLabel x u i
  let s:=if hit then m.set outB (-1) else m
  let t:=s.set ix ((k+1:ℕ):ℤ)
  have cv:s.reg (dest ix)=(k:ℤ):=by dsimp [s];split <;> exact st.counter
  have eq:flagStep.run x.n T m=t:=by
    have earlier:((k:ℤ)+1≤(i:ℤ)) ↔ k < i:=by omega
    have got:=read_label st.base st.scene (V ix) k st.counter
    have flagsEq:
       (P.test (plus (V ix) (E.lit 1)) (V gc)
        (.test (labelE (V ix)) (V refV) (.test (V refV) (labelE (V ix)) (.set outB (.lit (-1))) .nil) .nil) .nil).run x.n T m=s:=by
      simp only [P.run,plus_val,lit_val,st.counter,st.rem,got,st.key,earlier]
      by_cases k0:k < i
      · by_cases a:rawLabel x u k≤rawLabel x u i <;> by_cases b:rawLabel x u i≤rawLabel x u k
        · simp [s,hit,k0,a,b,le_antisymm a b]
        · simp [s,hit,k0,a,b,show rawLabel x u k≠rawLabel x u i by omega]
        · simp [s,hit,k0,a,b,show rawLabel x u k≠rawLabel x u i by omega]
        · omega
      · simp [s,hit,k0]
    change (inc ix).run x.n T _=t
    rw [flagsEq]
    simp [t,inc,P.run,cv]
  rw [eq]
  have keep (r:Reg) (h:r≠dest ix) (g:r≠dest outB) : t.reg r=m.reg r:=by
    dsimp [t,s];split <;> simp [h,g]
  have tm:t.mem=m.mem:=by dsimp [t,s];split <;> rfl
  refine ⟨⟨(keep _ (by decide) (by decide)).trans st.base,(keep _ (by decide) (by decide)).trans st.rem,
    by simp [t],(keep _ (by decide) (by decide)).trans st.key,?_,fun a=>(congrFun tm _).trans (st.scene a)⟩,tm⟩
  change t.reg (dest outB)=_
  rw [dup_succ];by_cases hk:hit
  · simp [t,s,hk,show dest outB≠dest ix by decide,show k < i ∧ rawLabel x u k=rawLabel x u i from hk]
  · simpa [t,s,hk,show dest outB≠dest ix by decide,show ¬(k < i ∧ rawLabel x u k=rawLabel x u i) from hk] using st.flag

theorem integer_part (x:World) (m:Model) (r:ℕ) (mem:∀a:ℕ,m.mem a=x.mem a)
    (pn:m.reg 0=(x.n:ℤ)) (slot:m.reg 3=(r:ℤ)) (hn:0<x.n) (hr:r<x.rows*x.n) :
    let u:=r/x.n;let i:=r%x.n;let t:=inspectRows.run x.n x.rows m
    (V tail).val t=((sceneBase x u:ℕ):ℤ) ∧
    (V outB).val t=(if i ∈ keys x u then 0 else -1) ∧ t.mem=m.mem := by
  let u:=r/x.n
  let i:=r%x.n
  let a:=coordinates.run x.n x.rows m
  obtain ⟨rem,base,ma⟩:=coordinate_values x m r pn slot hn hr
  have scene (j:ℕ) : a.mem j=x.mem j:=(congrFun ma _).trans (mem j)
  let b:=((a.set refV ((labelE (V gc)).val a)).set ix 0).set outB 0
  have init:Scan x u i 0 b:=by
    refine ⟨base,rem,rfl,?_,?_,scene⟩
    · exact read_label base scene (V gc) i rem
    · simp [b,Duplicate]
  have loop (k:ℕ) :
      let t:=(flagStep.run x.n x.rows)^[k] b
      Scan x u i k t ∧ t.mem=m.mem := by
    induction k with
    | zero=>exact ⟨init,ma⟩
    | succ k ih=>
      rw [Function.iterate_succ_apply']
      obtain ⟨s,e⟩:=flag_step x.rows u i k _ ih.1
      exact ⟨s,e.trans ih.2⟩
  obtain ⟨st,mm⟩:=loop x.n
  have hi:i<x.n:=Nat.mod_lt _ hn
  have iff:i∈keys x u ↔ ¬Duplicate x u i x.n:=by
    rw [key_iff x u ⟨i,hi⟩];apply not_congr;constructor
    · rintro ⟨j,hj,eq⟩;exact ⟨j,by omega,hj,eq⟩
    · rintro ⟨j,_,hj,eq⟩;exact ⟨j,hj,eq⟩
  refine ⟨st.base,?_,mm⟩
  change (V outB).val ((flagStep.run x.n x.rows)^[x.n] b)=_
  rw [st.flag]
  change (if Duplicate x u i x.n then _ else _)=(if i∈keys x u then _ else _)
  by_cases h:Duplicate x u i x.n
  · simp [h,show i∉keys x u from fun z=>iff.mp z h]
  · simp [h,iff.mpr h]

end StableMSR.Recovery.NativeWriter.Production.Classify
namespace StableMSR.Recovery.NativeWriter.Production.Classify
open Compiler OracleQueries WindowCSP WindowProfiles RAM Relative.Machine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

noncomputable def kind (x:World) (r:ℕ) : ℤ :=
  if r%x.n∈keys x (r/x.n) then if 0<scale x (r/x.n) then 0 else -2 else -1

def fetch : List Op := [.pointerCopy 28 (dest tail).val,.integerLoad 29 28,.pointerInc 28,.integerLoad 28 28,
  .distance 30 29 28,.pointerConst 14 (-1)]
def branch := Cmd.ite (.pointerLE (dest outB).val 14) (.atom (.pointerConst 6 (-1)))
  (.ite (.realNonpos 30) (.atom (.pointerConst 6 (-2))) (.atom (.pointerConst 6 0)))
def classifier := Cmd.seq (.atom (.pointerCopy 15 2)) (.seq (inspectRows.code 32) (.seq (line fetch) branch))

theorem sign_branch (x:World) (r:ℕ) (s:Store) (flag:s.ptrs (dest outB).val=(if r%x.n∈keys x (r/x.n) then 0 else -1))
    (dist:s.regs 30=scale x (r/x.n)) (neg:s.ptrs 14 = -1) :
    ∃t z,Executes x.dist branch s t z ∧ z≤5 ∧ t.imem=s.imem ∧ (∀i<6,t.ptrs i=s.ptrs i) ∧
      t.ptrs 6=kind x r ∧ t.ptrs 14 = -1 := by
  by_cases present:r%x.n∈keys x (r/x.n)
  · have no:¬(Cond.pointerLE (dest outB).val 14).test s:=by
      change ¬s.ptrs (dest outB).val ≤ s.ptrs 14;rw [flag,neg,if_pos present];decide
    by_cases nonpos:scale x (r/x.n)≤0
    · have yes:(Cond.realNonpos 30).test s:=by change s.regs 30≤0;rw [dist];exact nonpos
      exact ⟨_,_,.ite_false no (.ite_true yes (.atom (.pointerConst 6 (-2)) s)),by decide,rfl,
        fun j hj=>Function.update_of_ne (by omega) ..,by simp [Op.eval,kind,present,not_lt.mpr nonpos],neg⟩
    · have no':¬(Cond.realNonpos 30).test s:=by change ¬s.regs 30≤0;rw [dist];exact nonpos
      exact ⟨_,_,.ite_false no (.ite_false no' (.atom (.pointerConst 6 0) s)),by decide,rfl,
        fun j hj=>Function.update_of_ne (by omega) ..,by simp [Op.eval,kind,present,lt_of_not_ge nonpos],neg⟩
  · have yes:(Cond.pointerLE (dest outB).val 14).test s:=by
      change s.ptrs (dest outB).val ≤ s.ptrs 14;rw [flag,neg,if_neg present]
    exact ⟨_,_,.ite_true yes (.atom (.pointerConst 6 (-1)) s),by decide,rfl,fun j hj=>Function.update_of_ne (by omega) ..,
      by simp [Op.eval,kind,present],neg⟩

theorem classify_run (x:World) (s:Store) (r:ℕ) (rd:Ready x s) (slot:s.ptrs 3=(r:ℤ))
    (hn:0<x.n) (hr:r<x.rows*x.n) :
    ∃t z,Executes x.dist classifier s t z ∧ z≤(inspectRows.weight+12)*(1+x.n)*(1+x.rows) ∧
    t.imem=s.imem ∧ (∀i<6,t.ptrs i=s.ptrs i) ∧ t.ptrs 6=kind x r ∧ t.ptrs 14 = -1 := by
  let a:=(Op.pointerCopy 15 2).eval x.dist s
  have low (i:ℕ) (hi:i<15) : a.ptrs i=s.ptrs i:=Function.update_of_ne (by omega) ..
  have pn:a.ptrs 0=(x.n:ℤ):=(low 0 (by decide)).trans (rd.1 .points)
  have len:a.ptrs 15=(x.rows:ℤ):=calc a.ptrs 15 = s.ptrs 2 := rfl
          _ = (x.rows:ℤ) := rd.1 .rows
  obtain ⟨u,z,go,cost,sim⟩:=RAM.execute x.dist x.rows inspectRows 32 (by decide) a ⟨pn,len⟩
  obtain ⟨base,flag,mem⟩:=integer_part x (model a) r rd.2 pn ((low 3 (by decide)).trans slot) hn hr
  rw [←sim.1] at base flag mem
  change u.ptrs (dest tail).val=((sceneBase x (r/x.n):ℕ):ℤ) at base
  change u.imem=s.imem at mem
  let t:=perform x.dist u fetch
  have reg (i:ℕ) (hi:i<14) : t.ptrs i=u.ptrs i:=by
    simp [t,fetch,perform,Op.eval,Function.update_of_ne (by omega:i≠14),Function.update_of_ne (by omega:i≠28),Function.update_of_ne (by omega:i≠29)]
  have hit:t.regs 30=scale x (r/x.n):=by
    have one:u.imem ((sceneBase x (r/x.n):ℕ)+1:ℤ)=x.mem (sceneBase x (r/x.n)+1):=by
      simpa [mem] using rd.2 (sceneBase x (r/x.n)+1)
    have sone:s.imem ((sceneBase x (r/x.n):ℕ)+1:ℤ)=x.mem (sceneBase x (r/x.n)+1):=by simpa only [mem] using one
    simp [t,fetch,perform,Op.eval,base,WindowCSP.scale,one,mem,rd.2,sone]
  have flag':t.ptrs (dest outB).val=(if r%x.n∈keys x (r/x.n) then 0 else -1):=by
    change u.ptrs (dest outB).val=_;exact flag
  obtain ⟨v,y,last,work,vm,vr,sign,neg⟩:=sign_branch x r t flag' hit (by simp [t,fetch,perform,Op.eval])
  refine ⟨v,_,.seq (.atom _ _) (.seq go (.seq (line_exec x.dist u _) last)),?_,vm.trans mem,?_,sign,neg⟩
  · have time:=time_bound inspectRows x.n x.rows true true (by decide)
    change 1+(z+(6+y))≤_
    simp only [fac,if_true] at time
    nlinarith [Nat.le_trans cost time,Nat.zero_le x.n,Nat.zero_le x.rows,Nat.zero_le (x.n*x.rows)]
  · intro i hi
    let j:Reg:=⟨i,by omega⟩
    have rv:=congrArg (fun m:Model=>m.reg j) sim.1
    exact (vr i hi).trans ((reg i (by omega)).trans (rv.trans ((inspectRows.fixed _ _ _ j (by dsimp [j];omega)).trans (low i (by omega)))))

end StableMSR.Recovery.NativeWriter.Production.Classify
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit
open scoped Classical
theorem solution :
  ∃ (A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (r:ℕ),Ready x s → s.ptrs 3=(r:ℤ) → 0<x.n → r<x.rows*x.n →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+x.rows) ∧ t.imem=s.imem ∧
      (∀i<6,t.ptrs i=s.ptrs i) ∧
      t.ptrs 6=(if r%x.n∈WindowProfiles.keys x (r/x.n) then if 0<scale x (r/x.n) then 0 else -2 else -1) ∧
      t.ptrs 14 = -1 := by
  refine ⟨Classify.inspectRows.weight+12,Classify.classifier,?_⟩
  exact Classify.classify_run
