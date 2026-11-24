-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.native_candidate_filter
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:41:31.511183+00:00
-- url     : https://prove2.me/submissions/789087f7-0893-406c-a2b7-961bee3ca5c1

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
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
namespace StableMSR.Recovery.NativeWriter.Relative.Machine
theorem word_inj {j f a b : ℕ} (hj : j<8) (hf : f<8) : word j a=word f b ↔ j=f ∧ a=b := by
  unfold word;omega


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
theorem cell_inj {a b i j : ℕ} (ha:a<8) (hb:b<8) : cell a i=cell b j ↔ a=b ∧ i=j := by
  unfold cell;rw [word_inj (by decide) (by decide)];omega
theorem cell_ne_word {a i j k : ℕ} (hk:k<7) : cell a i≠word k j := by
  unfold cell;rw [ne_eq,word_inj (by decide) (by omega)];omega
theorem word_ne_cell {a i j k : ℕ} (hk:k<7) : word k j≠cell a i := Ne.symm (cell_ne_word hk)

def seqs : List P→P | []=>.nil | p::ps=>.seq p (seqs ps)
def Fixed (m u : Model) := ∀r : Reg,r≠dest outB → r≠dest inB → r≠dest bitI → u.reg r=m.reg r
theorem Fixed.trans {m u v : Model} (a:Fixed m u) (b:Fixed u v) : Fixed m v :=
  fun r h k j=>(b r h k j).trans (a r h k j)
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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Machine
open RAM Compiler OracleQueries SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

abbrev pos : Var := 0
abbrev prior : Var := 1
abbrev row : Var := 2
abbrev mark : Var := 3
abbrev srcBase : Var := 5
abbrev dstBase : Var := 4
abbrev pix : Var := 6
abbrev valid : Var := 7
abbrev exitId : Var := 8

def raw (f:ℕ) (e:E) := C 5 (plus (eight e) (.lit (f:ℤ)))
def rv (f:ℕ) := E.read (raw f (V row))
def rawZ (f:ℕ) (z:ℤ) := cz 5 (8*z+(f:ℤ))
@[simp] theorem raw_val (f:ℕ) (e:E) (m:Model) : (raw f e).val m=rawZ f (e.val m) := by simp [raw,rawZ]
@[simp] theorem raw_nat (f j:ℕ) : rawZ f (j:ℤ)=inputCell f j := by simp [rawZ,inputCell,cz,cell,wz,word]

abbrev Mem := ℤ→ℤ
def Outside (q:ℤ) := ∀a, a≤4 → ∀j,q≠cell a j
def Frame (base m:Mem) := ∀q,Outside q → m q=base q
def mentions : Instr→Option ℕ | .need k | .seal k=>some k | _=>none
def relevant (xs:List Instr) (k:ℕ) := ∃op∈xs,mentions op=some k
def refWord (a:Option ℕ) : ℤ := match a with | none=>0 | some k=>(k:ℤ)+1
def Dict (xs:List Instr) (m:Mem) (D:ℕ→Option ℕ) := ∀k,relevant xs k → m (cell 4 k)=refWord (D k)
def At (n:ℕ) (m:Mem) (j:ℕ) (e:Event) := m (cell 1 j)=e.tag ∧ m (cell 2 j)=e.arg ∧
  ∀pts,e=.mask pts → ∀k<n,m (cell 3 (j*n+k))=e.bit k
def Prefix (n:ℕ) (m:Mem) (out:List Event) := ∀j (hj:j<out.length),At n m j out[j]

theorem outside_input (f j:ℕ) : Outside (inputCell f j) := by
  intro a ha k;unfold inputCell;rw [ne_eq,cell_inj (by decide) (by omega)];omega
theorem outside_scene (i:ℕ) : Outside (i:ℤ) := by intro a ha k;unfold cell word;omega
theorem outside_lane (f j:ℕ) (hf:f≤6) : Outside (word f j) := by intro a ha k;exact word_ne_cell (by omega)
theorem Frame.update {b m:Mem} (h:Frame b m) (a j:ℕ) (ha:a≤4) (v:ℤ) :
    Frame b (Function.update m (cell a j) v) := by
  intro q oq;rw [Function.update_of_ne (oq a ha j)];exact h q oq

theorem Prefix.cut {n:ℕ} {m:Mem} {l r:List Event} (h:Prefix n m (l++r)) : Prefix n m l := by
  intro j hj;have lt:j<(l++r).length:=by simp;omega
  simpa [List.getElem_append_left hj] using h j lt

theorem Prefix.append {n:ℕ} {m:Mem} {l:List Event} {e:Event} (h:Prefix n m l) (last:At n m l.length e) :
    Prefix n m (l++[e]) := by
  intro j hj
  by_cases b:j<l.length
  · simpa [List.getElem_append_left b] using h j b
  · have eq:j=l.length:=by simp at hj;omega
    subst j;simpa using last

theorem At.change {n j:ℕ} {m t:Mem} {e:Event} (h:At n m j e)
    (a:t (cell 1 j)=m (cell 1 j)) (b:t (cell 2 j)=m (cell 2 j))
    (c:∀i<n,t (cell 3 (j*n+i))=m (cell 3 (j*n+i))) : At n t j e :=
  ⟨a.trans h.1,b.trans h.2.1,fun pts eq i hi=>(c i hi).trans (h.2.2 pts eq i hi)⟩

theorem dictionary_store {n:ℕ} {m:Mem} {l:List Event} (out:Prefix n m l) (k:ℕ) (z:ℤ) :
    Prefix n (Function.update m (cell 4 k) z) l := by
  intro j hj;apply (out j hj).change <;> intros <;> apply Function.update_of_ne <;>
    unfold cell word <;> push_cast <;> omega

theorem dict_insert {m:Mem} {xs:List Instr} {D:ℕ→Option ℕ} (h:Dict xs m D) (k v:ℕ) :
    Dict xs (Function.update m (cell 4 k) ((v:ℤ)+1)) (Function.update D k (some v)) := by
  intro j hj
  by_cases eq:j=k
  · subst j;simp [refWord]
  · simp [Function.update_of_ne eq,Function.update_of_ne (show cell 4 j≠cell 4 k by simp [cell_inj (by decide:4<8) (by decide:4<8),eq]),h j hj]

structure Snapshot (n i:ℕ) (xs:List Instr) (base:Mem) (m:Model) (s:Work) : Prop where
  frame : Frame base m.mem
  prefixOK : Prefix n m.mem (buffer s)
  dict : Dict xs m.mem s.dict
  index : (V row).val m=(i:ℤ)
  cursor : (V pos).val m=((buffer s).length:ℤ)
  committed : (V mark).val m=(s.done.length:ℤ)
  acc : (V prior).val m=(s.acc:ℤ)
  flag : (V valid).val m=(if s.ok then 1 else 0)
  exit : (V exitId).val m=(s.exit:ℤ)

def primeOne := P.put (C 4 (rv 2)) (.lit 0)
def prime := P.seq (.set row (.lit 0)) (.rep .events (.seq primeOne (inc row)))

end StableMSR.Recovery.NativeWriter.Production.Candidates.Machine

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Machine
open RAM Compiler OracleQueries SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
def copycalcStep := P.seq (.set outB (plus (V outB) (V pos))) (.set inB (plus (V inB) (V ix)))
def copyproducts := seqs [.set outB (.lit 0),.set inB (.lit 0),.rep .points copycalcStep]
def copybitStep (useMask : Bool) := P.seq
  (.put (C 3 (plus (V outB) (V bitI)))
    (if useMask then .read (raw 3 (plus (V inB) (V bitI))) else .lit 0)) (inc bitI)
def copywriteBits (useMask : Bool) := seqs [copyproducts,.set bitI (.lit 0),.rep .points (copybitStep useMask)]

theorem copyproducts_spec (n T : ℕ) (m : Model) :
    let u:=copyproducts.run n T m
    u.mem=m.mem ∧ Fixed m u ∧ u.reg (dest outB)=(n:ℤ)*(V pos).val m ∧ u.reg (dest inB)=(n:ℤ)*(V ix).val m := by
  let a:=(m.set outB 0).set inB 0
  have loop (k:ℕ) :
      let u:=(copycalcStep.run n T)^[k] a
      u.mem=m.mem ∧ Fixed m u ∧ u.reg (dest outB)=(k:ℤ)*(V pos).val m ∧ u.reg (dest inB)=(k:ℤ)*(V ix).val m := by
    induction k with
    | zero=>
      dsimp only [Function.iterate_zero_apply]
      refine ⟨rfl,?_,?_,?_⟩
      · intro r h k j;simp [a,h,k]
      · simp [a,dest]
      · simp [a,dest]
    | succ k ih=>
      rw [Function.iterate_succ_apply']
      let t:=(copycalcStep.run n T)^[k] a
      obtain ⟨mem,keep,o,i⟩:=ih
      have ph:(V pos).val t=(V pos).val m:=keep _ (by decide) (by decide) (by decide)
      have ex:(V ix).val t=(V ix).val m:=keep _ (by decide) (by decide) (by decide)
      refine ⟨mem,?_,?_,?_⟩
      · intro r hr hr' hq;simpa [copycalcStep,P.run,hr,hr'] using keep r hr hr' hq
      · change ((t.set outB _).set inB _).reg (dest outB)=_
        simp only [set_reg,show dest outB ≠ dest inB by decide,if_false,if_true,plus_val,V_val]
        change t.reg (dest outB)+(V pos).val t=_
        rw [o,ph];simp only [V_val];push_cast;ring
      · change ((t.set outB _).set inB _).reg (dest inB)=_
        simp only [P.run,set_reg,if_true,plus_val,V_val,show dest inB≠dest outB by decide,show dest ix≠dest outB by decide,if_false]
        rw [i,show t.reg (dest ix)=(V ix).val m from ex];simp only [V_val];push_cast;ring
  exact loop n

def copyBits (m u : Model) (A B k : ℕ) (useMask : Bool) :=
  (∀j<k,u.mem (cell 3 (A+j))=if useMask then m.mem (inputCell 3 (B+j)) else 0) ∧
  ∀q,(∀j<k,q≠cell 3 (A+j)) → u.mem q=m.mem q

theorem copybit_loop (n T k A B : ℕ) (useMask : Bool) (m : Model)
    (outB0 : m.reg (dest outB)=(A:ℤ)) (inB0 : m.reg (dest inB)=(B:ℤ)) (start : m.reg (dest bitI)=0) :
    let u:=((copybitStep useMask).run n T)^[k] m
    (∀r:Reg,r≠dest bitI → u.reg r=m.reg r) ∧ u.reg (dest bitI)=(k:ℤ) ∧ copyBits m u A B k useMask := by
  induction k with
  | zero=>exact ⟨fun _ _=>rfl,start,fun _ hj=>by omega,fun _ _=>rfl⟩
  | succ k ih=>
    let t:=((copybitStep useMask).run n T)^[k] m
    have rt:=ih.1
    have k0:t.reg (dest bitI)=(k:ℤ):=ih.2.1
    have o:t.reg (dest outB)=(A:ℤ):=(rt _ (by decide)).trans outB0
    have i:t.reg (dest inB)=(B:ℤ):=(rt _ (by decide)).trans inB0
    have old: t.mem (inputCell 3 (B+k))=m.mem (inputCell 3 (B+k)):=ih.2.2.2 _ (fun j _=>outside_input 3 (B+k) 3 (by decide) (A+j))
    let u:=(copybitStep useMask).run n T t
    have mem (q:ℤ) : u.mem q=if q=cell 3 (A+k) then (if useMask then m.mem (inputCell 3 (B+k)) else 0) else t.mem q := by
      cases useMask <;> simp only [u,copybitStep,P.run,inc,set_mem,put_mem,C_val,raw_val,plus_val,V_val,lit_val,read_val,k0,o,i,←Nat.cast_add,cz_nat,raw_nat,Bool.false_eq_true,if_false,if_true,old]
    rw [Function.iterate_succ_apply']
    change (∀r:Reg,r≠dest bitI → u.reg r=_) ∧ u.reg (dest bitI)=_ ∧ copyBits m u A B (k+1) useMask
    refine ⟨?_,?_,?_,?_⟩
    · intro r h;exact (by simp only [u,copybitStep,P.run,inc,set_reg,if_neg h,put_reg] : u.reg r=t.reg r).trans (rt r h)
    · simp [u,copybitStep,P.run,inc,k0]
    · intro j hj;rw [mem]
      by_cases eq:j=k
      · simp [eq]
      · rw [if_neg (by simp [cell_inj (by decide:3<8) (by decide:3<8)];omega)]
        exact ih.2.2.1 j (by omega)
    · intro q h;rw [mem,if_neg (h k (by omega))];exact ih.2.2.2 q (fun j hj=>h j (by omega))

theorem copybits_spec (n T P0 i : ℕ) (useMask : Bool) (m : Model)
    (phys0 : (V pos).val m=(P0:ℤ)) (ix0 : (V ix).val m=(i:ℤ)) :
    let u:=(copywriteBits useMask).run n T m
    Fixed m u ∧ copyBits m u (P0*n) (i*n) n useMask := by
  let a:=copyproducts.run n T m
  let b:=a.set bitI 0
  obtain ⟨ma,ka,aa,ia⟩:=copyproducts_spec n T m
  have outB0:b.reg (dest outB)=((P0*n:ℕ):ℤ):=by simpa [b,a,show dest outB≠dest bitI by decide,aa,phys0,mul_comm]
  have inB0:b.reg (dest inB)=((i*n:ℕ):ℤ):=by simpa [b,a,show dest inB≠dest bitI by decide,ia,ix0,mul_comm]
  obtain ⟨rt,_,hit,keep⟩:=copybit_loop n T n (P0*n) (i*n) useMask b outB0 inB0 (by simp [b])
  refine ⟨?_,?_,?_⟩
  · intro r ro ri rb
    exact (rt r rb).trans ((by simp [b,rb] : b.reg r=a.reg r).trans (ka r ro ri rb))
  · intro j hj;exact (hit j hj).trans (by simp [b,a,ma])
  · intro q h;exact (keep q h).trans (congrFun ma q)

end StableMSR.Recovery.NativeWriter.Production.Candidates.Machine

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Machine
open RAM Compiler OracleQueries SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
theorem nat_arg (e:Instr) : (e.arg.toNat:ℤ)=e.arg := by
  cases e <;> simp [Instr.arg]
  rename_i b;cases b <;> decide

theorem rv_value (f i:ℕ) (m:Model) (h:(V row).val m=(i:ℤ)) : (rv f).val m=m.mem (inputCell f i) := by
  simp only [rv,read_val,raw_val,h,raw_nat]

def freshRegs := seqs [.set pos (.lit 0),.set prior (.lit 0),.set mark (.lit 0),.set row (.lit 0),
  .set valid (.lit 1),.set exitId (.lit 0)]
def init := P.seq prime freshRegs

theorem prime_ok (n:ℕ) (xs:List Instr) (m:Model) (input:Input n m.mem xs) :
    Snapshot n 0 xs m.mem (init.run n xs.length m) start := by
  let base:=m.set row 0
  let body:=P.seq primeOne (inc row)
  have loop (k:ℕ) (hk:k≤xs.length) :
      let t:=(body.run n xs.length)^[k] base
      Frame m.mem t.mem ∧ (V row).val t=(k:ℤ) ∧
      ∀j (hj:j<k),t.mem (cell 4 (xs[j]'(by omega)).arg.toNat)=0 := by
    induction k with
    | zero=>exact ⟨fun _ _=>rfl,by simp [base],fun _ hj=>by omega⟩
    | succ k ih=>
      have lt:k<xs.length:=by omega
      let t:=(body.run n xs.length)^[k] base
      obtain ⟨fr,idx,zero⟩:=ih (by omega)
      let key:=xs[k].arg.toNat
      have rd:(rv 2).val t=(key:ℤ):=by
        rw [rv_value 2 k t idx,fr _ (outside_input 2 k),(input.2 k lt).2.1,nat_arg]
      have one:body.run n xs.length t=(t.put (cell 4 key) 0).set row ((k:ℤ)+1):=by
        simp only [body,primeOne,inc,P.run,C_val,rd,cz_nat,lit_val,plus_val,V_val,put_reg]
        rw [show t.reg (dest row)=(k:ℤ) from idx]
      rw [Function.iterate_succ_apply'];change Frame _ (body.run _ _ t).mem ∧ _
      rw [one];refine ⟨fr.update _ _ (by decide) _,by simp,?_⟩
      intro j hj
      by_cases same:(xs[j]'(by omega)).arg.toNat=key
      · simp [same]
      · have neq:j≠k:=by rintro rfl;exact same rfl
        simpa only [set_mem,put_mem,cell_inj (by decide:4<8) (by decide:4<8),true_and,if_neg same] using zero j (by omega)
  let t:=prime.run n xs.length m
  obtain ⟨fr,_,zero⟩:=loop xs.length (by rfl)
  have ft:Frame m.mem t.mem:=fr
  have dict:Dict xs t.mem start.dict:=by
    intro key rel
    obtain ⟨e,em,ke⟩:=rel
    obtain ⟨j,lj,eq⟩:=List.mem_iff_getElem.mp em
    have val:e.arg.toNat=key:=by cases e <;> simp_all [mentions,Instr.arg]
    rw [←val,←eq];exact zero j lj
  change Snapshot n 0 xs m.mem (freshRegs.run n xs.length t) start
  refine ⟨ft,fun j hj=>by simp [buffer,start] at hj,dict,?_,?_,?_,?_,?_,?_⟩ <;>
    simp [freshRegs,seqs,P.run,dest,buffer,start]
end StableMSR.Recovery.NativeWriter.Production.Candidates.Machine

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Machine
open RAM Compiler OracleQueries SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
def metadata (tag:ℤ) (arg:E) := P.seq (.put (C 2 (V pos)) arg) (.put (C 1 (V pos)) (.lit tag))
def appendEvent (tag:ℤ) (arg:E) := seqs [metadata tag arg,copywriteBits true,inc pos]

structure Pushed (n:ℕ) (xs:List Instr) (base:Mem) (m t:Model) (s:Work) (ev:Event) : Prop where
  frame : Frame base t.mem
  prefixOK : Prefix n t.mem (buffer s++[ev])
  dict : Dict xs t.mem s.dict
  cursor : t.reg (dest pos)=(((buffer s).length+1:ℕ):ℤ)
  rowReg : t.reg (dest row)=m.reg (dest row)
  markReg : t.reg (dest mark)=m.reg (dest mark)
  accReg : t.reg (dest prior)=m.reg (dest prior)
  flagReg : t.reg (dest valid)=m.reg (dest valid)
  exitReg : t.reg (dest exitId)=m.reg (dest exitId)

theorem push_event {n i T:ℕ} {xs:List Instr} {base:Mem} {m:Model} {s:Work}
    (h:Snapshot n i xs base m s) (ev:Event) (arg:E) (ha:arg.val m=ev.arg)
    (mask:∀pts,ev=.mask pts → ∀k<n,base (inputCell 3 (i*n+k))=ev.bit k) :
    Pushed n xs base m ((appendEvent ev.tag arg).run n T m) s ev := by
  let p:=(buffer s).length
  let a:=(metadata ev.tag arg).run n T m
  let b:=(copywriteBits true).run n T a
  have headEq:a=(m.put (cell 2 p) ev.arg).put (cell 1 p) ev.tag:=by
    simp only [a,metadata,P.run,C_val,h.cursor,cz_nat,ha,lit_val,V_val,put_reg]
    rw [show m.reg (dest pos)=(p:ℤ) from h.cursor,cz_nat]
  have regs:a.reg=m.reg:=rfl
  have af:Frame base a.mem:=by rw [headEq];exact (h.frame.update _ _ (by decide) _).update _ _ (by decide) _
  obtain ⟨fixed,bits⟩:=copybits_spec n T p i true a h.cursor h.index
  have nxt:(appendEvent ev.tag arg).run n T m=b.set pos (((p+1:ℕ):ℤ)):=by
    change b.set pos (b.reg (dest pos)+1)=_
    rw [(fixed _ (by decide) (by decide) (by decide)).trans ((congrFun regs _).trans h.cursor)];rfl
  rw [nxt]
  have keep (r:Reg) (rp:r≠dest pos) (ro:r≠dest outB) (ri:r≠dest inB) (rb:r≠dest bitI) :
      (b.set pos (((p+1:ℕ):ℤ))).reg r=m.reg r:=by
    rw [set_reg,if_neg rp];exact (fixed r ro ri rb).trans (congrFun regs r)
  have untouched (q:ℤ) (x:q≠cell 1 p) (y:q≠cell 2 p) (z:∀k<n,q≠cell 3 (p*n+k)) :
      b.mem q=m.mem q:=by rw [bits.2 q z,headEq];simp [x,y]
  have fr:Frame base b.mem:=by
    intro q oq;rw [bits.2 q (fun k _=>oq 3 (by decide) _),af q oq]
  have cols {u j v k:ℕ} (hu:u<8) (hv:v<8) (ne:u≠v) : cell u j≠cell v k:=by simp [cell_inj hu hv,ne]
  have head:Prefix n b.mem (buffer s):=by
    intro j hj
    have jp:j<p:=hj
    apply (h.prefixOK j hj).change
    · apply untouched _ _ (cols (by decide) (by decide) (by decide)) (fun _ _=>cols (by decide) (by decide) (by decide))
      simp [cell_inj (by decide:1<8) (by decide:1<8),Nat.ne_of_lt jp]
    · apply untouched _ (cols (by decide) (by decide) (by decide)) _ (fun _ _=>cols (by decide) (by decide) (by decide))
      simp [cell_inj (by decide:2<8) (by decide:2<8),Nat.ne_of_lt jp]
    · intro k hk;apply untouched _ (cols (by decide) (by decide) (by decide)) (cols (by decide) (by decide) (by decide))
      intro z hz
      have sep:=Nat.mul_le_mul_right n (show j+1≤p by omega)
      simp only [Nat.add_mul,Nat.one_mul] at sep
      simp [cell_inj (by decide:3<8) (by decide:3<8)];omega
  have last:At n b.mem p ev:=by
    refine ⟨?_,?_,?_⟩
    · rw [bits.2 _ (fun _ _=>cols (by decide) (by decide) (by decide)),headEq];simp
    · rw [bits.2 _ (fun _ _=>cols (by decide) (by decide) (by decide)),headEq]
      simp [cols (u:=2) (v:=1) (by decide) (by decide) (by decide)]
    · intro pts eq k hk;change b.mem (cell 3 (p*n+k))=_
      rw [bits.1 k hk,if_pos rfl,af _ (outside_input _ _)];exact mask pts eq k hk
  refine ⟨fr,head.append last,?_,by simp [p],keep _ (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide),keep _ (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide),keep _ (by decide) (by decide) (by decide) (by decide)⟩
  intro k hk;change b.mem (cell 4 k)=_
  rw [untouched _ (cols (by decide) (by decide) (by decide)) (cols (by decide) (by decide) (by decide))
    (fun _ _=>cols (by decide) (by decide) (by decide)),h.dict k hk]
end StableMSR.Recovery.NativeWriter.Production.Candidates.Machine

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Machine
open RAM Compiler OracleQueries SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
def keyValue := E.read (C 4 (rv 2))
def writeLit := appendEvent 0 (.lit 0)
def child := P.test (.lit 1) keyValue (appendEvent 1 (sub keyValue (.lit 1)))
  (.seq (appendEvent 1 (.lit 0)) (.set valid (.lit 0)))
def sealRow := P.seq (.put (C 4 (rv 2)) (plus (V prior) (.lit 1))) (.set prior (.lit 0))
def commit (v:Var) := seqs [.set mark (V pos),.set v (V pos),.set valid (.lit 1)]
def discard := P.seq (.set pos (V mark)) (.set valid (.lit 1))
def acceptTrial := P.seq (appendEvent 2 (V prior)) (commit prior)
def acceptRoot := P.seq (appendEvent 3 (.lit 0)) (commit exitId)
def failRoot := P.seq discard (.set exitId (.lit 0))
def closeTrial := P.test (.lit 1) (V valid) (.test (.lit 1) (rv 2) acceptTrial discard) discard
def finishRoot := P.test (.lit 1) (V valid) acceptRoot failRoot
def choose := P.test (rv 1) (.lit 0) writeLit (.test (rv 1) (.lit 1) child
  (.test (rv 1) (.lit 2) closeTrial (.test (rv 1) (.lit 3) sealRow finishRoot)))
def advance := P.seq choose (inc row)

theorem do_lit {n T i:ℕ} {xs:List Instr} {base:Mem} {m:Model} {s:Work}
    (snap:Snapshot n i xs base m s) (pts:List ℕ)
    (bits:∀k<n,base (inputCell 3 (i*n+k))=(if pts.contains k then 1 else 0)) :
    Snapshot n i xs base (writeLit.run n T m) (step s (.lit pts)) := by
  have h:=push_event (T:=T) snap (.mask pts) (.lit 0) rfl (fun _ _=>bits)
  refine ⟨h.frame,?_,h.dict,h.rowReg.trans snap.index,?_,h.markReg.trans snap.committed,
    h.accReg.trans snap.acc,h.flagReg.trans snap.flag,h.exitReg.trans snap.exit⟩
  · simpa only [writeLit,Event.tag,buffer,step,List.append_assoc] using h.prefixOK
  · simpa [writeLit,Event.tag,buffer,step,Nat.add_assoc] using h.cursor

theorem do_child {n T i:ℕ} {xs:List Instr} {base:Mem} {m:Model} {s:Work}
    (snap:Snapshot n i xs base m s) (k:ℕ) (seen:relevant xs k) (arg:(rv 2).val m=(k:ℤ)) :
    Snapshot n i xs base (child.run n T m) (step s (.need k)) := by
  have rd:keyValue.val m=refWord (s.dict k):=by
    simp only [keyValue,read_val,C_val,arg,cz_nat,snap.dict k seen]
  cases lookup:s.dict k with
  | some j=>
    have val:keyValue.val m=(j:ℤ)+1:=by simpa [lookup,refWord] using rd
    have add:(sub keyValue (.lit 1)).val m=(Event.child j).arg:=by simp [val,Event.arg]
    have h:=push_event (T:=T) snap (.child j) (sub keyValue (.lit 1)) add (by intro _ h;cases h)
    unfold child;dsimp only [P.run];rw [if_pos (by simp [val])]
    refine ⟨h.frame,?_,h.dict,h.rowReg.trans snap.index,?_,h.markReg.trans snap.committed,
      h.accReg.trans snap.acc,?_,h.exitReg.trans snap.exit⟩
    · simpa only [writeLit,Event.tag,buffer,step,lookup,Option.getD_some,List.append_assoc] using h.prefixOK
    · simpa [writeLit,Event.tag,buffer,step,lookup,Nat.add_assoc] using h.cursor
    · simpa [Event.tag,step,lookup] using h.flagReg.trans snap.flag
  | none=>
    have val:keyValue.val m=0:=by simpa [lookup,refWord] using rd
    have h:=push_event (T:=T) snap (.child 0) (.lit 0) rfl (by intro _ h;cases h)
    let t:=(appendEvent 1 (.lit 0)).run n T m
    have eq:child.run n T m=t.set valid 0:=by unfold child;simp only [P.run,lit_val,val];rfl
    rw [eq]
    refine ⟨h.frame,?_,h.dict,?_,?_,?_,?_,?_,?_⟩
    · simpa [t,Event.tag,buffer,step,lookup,List.append_assoc] using h.prefixOK
    · exact (by rfl : (V row).val (t.set valid 0)=t.reg (dest row)).trans (h.rowReg.trans snap.index)
    · change t.reg (dest pos)=_;simpa [t,Event.tag,step,buffer,lookup,Nat.add_assoc] using h.cursor
    · exact h.markReg.trans snap.committed
    · exact h.accReg.trans snap.acc
    · simp [step,lookup]
    · exact h.exitReg.trans snap.exit

theorem do_seal {n T i:ℕ} {xs:List Instr} {base:Mem} {m:Model} {s:Work}
    (snap:Snapshot n i xs base m s) (k:ℕ) (arg:(rv 2).val m=(k:ℤ)) :
    Snapshot n i xs base (sealRow.run n T m) (step s (.seal k)) := by
  have eq:sealRow.run n T m=(m.put (cell 4 k) ((s.acc:ℤ)+1)).set prior 0:=by
    simp only [sealRow,P.run,C_val,arg,cz_nat,plus_val,snap.acc,lit_val]
  rw [eq]
  exact ⟨snap.frame.update _ _ (by decide) _,dictionary_store snap.prefixOK _ _,dict_insert snap.dict _ _,
    snap.index,snap.cursor,snap.committed,by simp [step],snap.flag,snap.exit⟩
end StableMSR.Recovery.NativeWriter.Production.Candidates.Machine

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Machine
open RAM Compiler OracleQueries SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
def lost (s:Work) : Work := {s with stage:=[],ok:=true}

theorem on_discard {n T i:ℕ} {xs:List Instr} {base:Mem} {m:Model} {s:Work}
    (h:Snapshot n i xs base m s) : Snapshot n i xs base (discard.run n T m) (lost s) := by
  refine ⟨h.frame,?_,h.dict,h.index,?_,h.committed,h.acc,?_,h.exit⟩
  · simpa only [lost,buffer,List.append_nil,discard,P.run,set_mem] using Prefix.cut h.prefixOK
  · simpa [buffer,discard,P.run,lost,dest] using h.committed
  · simp [discard,P.run,lost]

theorem on_accept {n T i:ℕ} {xs:List Instr} {base:Mem} {m:Model} {s:Work}
    (h:Snapshot n i xs base m s) :
    let out:=buffer s++[.join s.acc]
    Snapshot n i xs base (acceptTrial.run n T m) {s with done:=out,stage:=[],ok:=true,acc:=out.length} := by
  let out:=buffer s++[.join s.acc]
  let t:=(appendEvent 2 (V prior)).run n T m
  have p:=push_event (T:=T) h (.join s.acc) (V prior) h.acc (by intro _ h;cases h)
  have sz:t.reg (dest pos)=(out.length:ℤ):=by simpa [t,out,Event.tag] using p.cursor
  have eq:acceptTrial.run n T m=((t.set mark (t.reg (dest pos))).set prior (t.reg (dest pos))).set valid 1:=rfl
  rw [eq];refine ⟨p.frame,?_,p.dict,p.rowReg.trans h.index,?_,?_,?_,by rfl,p.exitReg.trans h.exit⟩
  · simpa only [buffer,List.append_nil,set_mem,t,Event.tag] using p.prefixOK
  · change t.reg (dest pos)=_;simpa [buffer,out] using sz
  · exact sz
  · exact sz

theorem on_root {n T i:ℕ} {xs:List Instr} {base:Mem} {m:Model} {s:Work}
    (h:Snapshot n i xs base m s) :
    let out:=buffer s++[.save]
    Snapshot n i xs base (acceptRoot.run n T m) {s with done:=out,stage:=[],ok:=true,exit:=out.length} := by
  let out:=buffer s++[.save]
  let t:=(appendEvent 3 (.lit 0)).run n T m
  have p:=push_event (T:=T) h .save (.lit 0) rfl (by intro _ h;cases h)
  have sz:t.reg (dest pos)=(out.length:ℤ):=by simpa [t,out,Event.tag] using p.cursor
  have eq:acceptRoot.run n T m=((t.set mark (t.reg (dest pos))).set exitId (t.reg (dest pos))).set valid 1:=rfl
  rw [eq];refine ⟨p.frame,?_,p.dict,p.rowReg.trans h.index,?_,?_,p.accReg.trans h.acc,by rfl,sz⟩
  · simpa only [buffer,List.append_nil,set_mem,t,Event.tag] using p.prefixOK
  · change t.reg (dest pos)=_;simpa [buffer,out] using sz
  · exact sz

theorem do_close {n T i:ℕ} {xs:List Instr} {base:Mem} {m:Model} {s:Work}
    (h:Snapshot n i xs base m s) (good:Bool) (arg:(rv 2).val m=(if good then 1 else 0)) :
    Snapshot n i xs base (closeTrial.run n T m) (step s (.close good)) := by
  cases ok:s.ok <;> cases good <;>
    simp only [closeTrial,P.run,lit_val,h.flag,ok,Bool.false_eq_true,if_false,ite_true,
      step,Bool.false_and,Bool.true_and,arg] <;> norm_num <;>
    first | exact on_discard h | simpa only [List.length_append,List.length_singleton] using (on_accept (T:=T) h)

theorem do_finish {n T i:ℕ} {xs:List Instr} {base:Mem} {m:Model} {s:Work}
    (h:Snapshot n i xs base m s) : Snapshot n i xs base (finishRoot.run n T m) (step s .finish) := by
  cases ok:s.ok
  · have old:=on_discard (T:=T) h
    have eq:finishRoot.run n T m=(discard.run n T m).set exitId 0:=by
      unfold finishRoot;simp only [P.run,h.flag,ok,lit_val,Bool.false_eq_true,if_false];rfl
    have eq':step s .finish={lost s with exit:=0}:=by simp [step,ok,lost]
    rw [eq,eq'];exact ⟨old.frame,old.prefixOK,old.dict,old.index,old.cursor,old.committed,old.acc,old.flag,by simp⟩
  · simpa only [finishRoot,P.run,lit_val,h.flag,ok,ite_true,le_refl,step] using (on_root (T:=T) h)
end StableMSR.Recovery.NativeWriter.Production.Candidates.Machine

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Machine
open RAM Compiler OracleQueries SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
theorem advance_ok {n T i:ℕ} {xs:List Instr} {base:Mem} {m:Model} {s:Work}
    (h:Snapshot n i xs base m s) (input:Input n base xs) (hi:i<xs.length) :
    Snapshot n (i+1) xs base (advance.run n T m) (step s xs[i]) := by
  have mem:xs[i]∈xs:=List.getElem_mem ..
  have val (f:ℕ) : (rv f).val m=base (inputCell f i):=(rv_value f i m h.index).trans (h.frame _ (outside_input f i))
  obtain ⟨ht,ha,mask⟩:=input.2 i hi
  have tag: (rv 1).val m=xs[i].tag:=(val 1).trans ht
  have ar: (rv 2).val m=xs[i].arg:=(val 2).trans ha
  have one:Snapshot n i xs base (choose.run n T m) (step s xs[i]) := by
    cases eq:xs[i] with
    | lit pts=>
      have b:∀k<n,base (inputCell 3 (i*n+k))=(if pts.contains k then 1 else 0):=mask pts eq
      simpa only [choose,P.run,tag,eq,Instr.tag,lit_val,le_refl,ite_true] using (do_lit (T:=T) h pts b)
    | need k=>
      have rel:relevant xs k:=⟨xs[i],mem,by rw [eq];rfl⟩
      rw [eq] at ar tag
      unfold choose;simp only [P.run,tag,Instr.tag,lit_val];norm_num
      exact do_child h k rel ar
    | close b=>
      rw [eq] at ar tag
      unfold choose;simp only [P.run,tag,Instr.tag,lit_val];norm_num
      exact do_close h b ar
    | «seal» k=>
      rw [eq] at ar tag
      unfold choose;simp only [P.run,tag,Instr.tag,lit_val];norm_num
      exact do_seal h k ar
    | finish=>
      rw [eq] at tag
      unfold choose;simp only [P.run,tag,Instr.tag,lit_val];norm_num
      exact do_finish h
  let t:=choose.run n T m
  have next:advance.run n T m=t.set row ((i:ℤ)+1):=by
    change t.set row ((V row).val t+1)=_;rw [one.index]
  rw [next];refine ⟨one.frame,one.prefixOK,one.dict,by simp,one.cursor,one.committed,one.acc,one.flag,one.exit⟩

def mainPass := P.rep .events advance
def headers := P.seq (.put (C 0 (.lit 0)) (V mark)) (.put (C 0 (.lit 1)) (V exitId))
def filterCode := seqs [init, mainPass, headers]

theorem output_ok (n:ℕ) (xs:List Instr) (m:Model) (input:Input n m.mem xs) :
    let t:=filterCode.run n xs.length m
    Frame m.mem t.mem ∧ Stored n t.mem (Candidates.eval xs) := by
  let a:=init.run n xs.length m
  let T:=xs.length
  have loop (j:ℕ) (hj:j≤xs.length) :
      Snapshot n j xs m.mem ((advance.run n T)^[j] a) ((xs.take j).foldl step start) := by
    induction j with
    | zero=>exact prime_ok n xs m input
    | succ j ih=>
      have lt:j<xs.length:=by omega
      rw [Function.iterate_succ_apply',List.take_succ_eq_append_getElem lt,List.foldl_append]
      exact advance_ok (ih (by omega)) input lt
  let v:=mainPass.run n T a
  let s:=xs.foldl step start
  have h:Snapshot n xs.length xs m.mem v s:=by
    simpa only [v,mainPass,P.run,Axis.len,T,s,List.take_length] using loop xs.length (by rfl)
  have prefixOK:Prefix n v.mem s.done:=Prefix.cut h.prefixOK
  let t:=filterCode.run n T m
  have eq:t=(v.put (cell 0 0) s.done.length).put (cell 0 1) s.exit:=by
    change (headers.run n T v)=_
    simp only [headers,P.run,C_val,lit_val,h.committed,V_val,put_reg]
    rw [show v.reg (dest exitId)=(s.exit:ℤ) from h.exit];rfl
  have fr:Frame m.mem t.mem:=by rw [eq];exact (h.frame.update _ _ (by decide) _).update _ _ (by decide) _
  have mem (b j:ℕ) (hb:0<b) (hb':b<8) : t.mem (cell b j)=v.mem (cell b j):=by
    rw [eq];simp [cell_inj hb' (by decide:0<8),Nat.ne_of_gt hb]
  refine ⟨fr,?_,?_,?_⟩
  · change t.mem (cell 0 0)=_;rw [eq];simp [cell_inj (by decide:0<8) (by decide:0<8),s,Candidates.eval]
  · change t.mem (cell 0 1)=_;rw [eq];simp [s,Candidates.eval]
  · intro j hj
    exact (prefixOK j hj).change (mem 1 _ (by decide) (by decide)) (mem 2 _ (by decide) (by decide))
      (fun _ _=>mem 3 _ (by decide) (by decide))
end StableMSR.Recovery.NativeWriter.Production.Candidates.Machine

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.Machine
open RAM Compiler OracleQueries SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
open Relative.Machine
def setupRaw : List Op := [.pointerConst 15 (inputCell 0 0),.integerLoad 15 15]
def nativeFilter := Cmd.seq (line setupRaw) (filterCode.code 32)

theorem native_filter : ∃ (A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (xs:List Candidates.Instr),
    Ready x s → Input x.n s.imem xs →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+xs.length) ∧ Ready x t ∧
      (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧ (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
      Stored x.n t.imem (Candidates.eval xs) := by
  refine ⟨filterCode.weight+2,nativeFilter,?_⟩
  intro x s xs ready input
  let T:=xs.length
  let b:=perform x.dist s setupRaw
  have reg (j:ℕ) (hj:j<15) : b.ptrs j=s.ptrs j:=by
    simp [b,setupRaw,perform,Op.eval,Function.update_of_ne (by omega:j≠15)]
  have sz:b.ptrs 15=(T:ℤ):=by simpa [b,setupRaw,perform,Op.eval,T] using input.1
  have fit:Fit x.n T b:=⟨(reg 0 (by decide)).trans (ready.1 .points),sz⟩
  obtain ⟨t,z,go,cost,sim⟩:=RAM.execute x.dist T filterCode 32 (by decide) b fit
  have out:=output_ok x.n xs (model b) input
  change Frame s.imem (filterCode.run x.n T (model b)).mem ∧ Stored x.n (filterCode.run x.n T (model b)).mem _ at out
  rw [←sim.1] at out
  have low (j:Reg) (hj:j.val<7) : t.ptrs j.val=s.ptrs j.val:=
    (congrArg (fun m:Model=>m.reg j) sim.1).trans ((filterCode.fixed x.n T _ _ (by omega)).trans (reg j.val (by omega)))
  refine ⟨t,2+z,.seq (line_exec x.dist s _) go,?_,⟨?_,?_⟩,?_,?_,out.2⟩
  · have tmp:=time_bound filterCode x.n T true true (by decide)
    have bound:z≤filterCode.weight*(1+x.n)*(1+T):=cost.trans (by simpa [fac,Nat.mul_assoc] using tmp)
    change 2+z≤(filterCode.weight+2)*(1+x.n)*(1+T)
    rw [Nat.add_mul,Nat.add_mul];nlinarith
  · intro ax;cases ax <;> first
      | exact (low 0 (by decide)).trans (ready.1 .points)
      | exact (low 1 (by decide)).trans (ready.1 .blocks)
      | exact (low 2 (by decide)).trans (ready.1 .rows)
  · intro j;exact (out.1 _ (outside_scene j)).trans (ready.2 j)
  · intro j hj;have small:j<7:=by simp at hj;omega
    exact low ⟨j,by omega⟩ small
  · intro j _ hj k;exact out.1 _ (outside_lane j k hj)
end StableMSR.Recovery.NativeWriter.Production.Candidates.Machine
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates
theorem solution :
    ∃ (A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (xs:List Candidates.Instr),Ready x s → Input x.n s.imem xs →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+xs.length) ∧ Ready x t ∧
      (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧ (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
      Stored x.n t.imem (Candidates.eval xs) := StableMSR.Recovery.NativeWriter.Production.Candidates.Machine.native_filter
