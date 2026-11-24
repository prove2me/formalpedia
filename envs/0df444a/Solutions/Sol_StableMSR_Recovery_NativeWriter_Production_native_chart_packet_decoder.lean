-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.native_chart_packet_decoder
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:20:53.73107+00:00
-- url     : https://prove2.me/submissions/5b9f444c-57f5-4028-8c12-5c152ea545ed

import Definitions.Def_StableMSR_RegionalProductionTable
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
namespace StableMSR.Recovery.NativeWriter.Production
open SingleCircuit TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem play_append (a b : List Event) : play (a++b)=b.foldl step (play a) := List.foldl_append
theorem memo_size (s : State) (es : List Event) : (es.foldl step s).memo.size=s.memo.size+es.length := by
  induction es generalizing s with
  | nil=>simp
  | cons e es ih=>
    have one : (step s e).memo.size=s.memo.size+1 := by cases e <;> simp [step]
    simp [ih,one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem play_size (es : List Event) : (play es).memo.size=es.length+1 := by
  simpa [play,initial,Nat.add_comm] using memo_size initial es

end StableMSR.Recovery.NativeWriter.Production
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
def phys := plus (.reg 4) (V gc)
def calcStep := P.seq (.set outB (plus (V outB) phys)) (.set inB (plus (V inB) (V ix)))
def products := seqs [.set outB (.lit 0),.set inB (.lit 0),.rep .points calcStep]
def bitStep (useMask : Bool) := P.seq
  (.put (W 5 (plus (V outB) (V bitI)))
    (if useMask then .read (C 3 (plus (V inB) (V bitI))) else .lit 0)) (inc bitI)
def writeBits (useMask : Bool) := seqs [products,.set bitI (.lit 0),.rep .points (bitStep useMask)]

inductive Arg where | zero | acc | ref | previous
def Arg.expr : Arg→E | .zero=>.lit 0 | .acc=>V tail | .ref=>V refV | .previous=>sub (V gc) (.lit 1)
def encoded (tag:ℤ) (a:Arg) := if 1≤tag then sub a.expr (V gc) else .lit 0
def fields (tag:ℤ) (a b:Arg) := seqs [.put (W 1 phys) (.lit tag),.put (W 2 phys) (encoded tag a),.put (W 3 phys) (encoded tag b)]
def emit (tag:ℤ) (useMask:Bool) (a b:Arg) := seqs [fields tag a b,writeBits useMask,inc gc]

def Fixed (m u : Model) := ∀r : Reg,r≠dest outB → r≠dest inB → r≠dest bitI → u.reg r=m.reg r
theorem Fixed.trans {m u v : Model} (a:Fixed m u) (b:Fixed u v) : Fixed m v :=
  fun r h k j=>(b r h k j).trans (a r h k j)
theorem products_spec (n T : ℕ) (m : Model) :
    let u:=products.run n T m
    u.mem=m.mem ∧ Fixed m u ∧ u.reg (dest outB)=(n:ℤ)*phys.val m ∧ u.reg (dest inB)=(n:ℤ)*(V ix).val m := by
  let a:=(m.set outB 0).set inB 0
  have loop (k:ℕ) :
      let u:=(calcStep.run n T)^[k] a
      u.mem=m.mem ∧ Fixed m u ∧ u.reg (dest outB)=(k:ℤ)*phys.val m ∧ u.reg (dest inB)=(k:ℤ)*(V ix).val m := by
    induction k with
    | zero=>
      dsimp only [Function.iterate_zero_apply]
      refine ⟨rfl,?_,?_,?_⟩
      · intro r h k j;simp [a,h,k]
      · simp [a,dest]
      · simp [a,dest]
    | succ k ih=>
      rw [Function.iterate_succ_apply']
      let t:=(calcStep.run n T)^[k] a
      obtain ⟨mem,keep,o,i⟩:=ih
      have ph:phys.val t=phys.val m:=by simp only [phys,plus_val,V_val,reg_val];rw [keep 4 (by decide) (by decide) (by decide),keep (dest gc) (by decide) (by decide) (by decide)]
      have ex:(V ix).val t=(V ix).val m:=keep _ (by decide) (by decide) (by decide)
      refine ⟨mem,?_,?_,?_⟩
      · intro r hr hr' hq;simpa [calcStep,P.run,hr,hr'] using keep r hr hr' hq
      · change ((t.set outB _).set inB _).reg (dest outB)=_
        simp only [set_reg,show dest outB ≠ dest inB by decide,if_false,if_true,plus_val,V_val]
        change t.reg (dest outB)+phys.val t=_
        rw [o,ph];push_cast;ring
      · change ((t.set outB _).set inB _).reg (dest inB)=_
        simp only [P.run,set_reg,if_true,plus_val,V_val,show dest inB≠dest outB by decide,show dest ix≠dest outB by decide,if_false]
        rw [i,show t.reg (dest ix)=(V ix).val m from ex];simp only [V_val];push_cast;ring
  exact loop n

end StableMSR.Recovery.NativeWriter.Production.RAM

namespace StableMSR.Recovery.NativeWriter.Production.RAM
open SingleCircuit SingleRAM Relative Relative.Machine Compiler OracleQueries
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

def Bits (m u : Model) (A B k : ℕ) (useMask : Bool) :=
  (∀j<k,u.mem (word 5 (A+j))=if useMask then m.mem (cell 3 (B+j)) else 0) ∧
  ∀q,(∀j<k,q≠word 5 (A+j)) → u.mem q=m.mem q

theorem bit_loop (n T k A B : ℕ) (useMask : Bool) (m : Model)
    (outB0 : m.reg (dest outB)=(A:ℤ)) (inB0 : m.reg (dest inB)=(B:ℤ)) (start : m.reg (dest bitI)=0) :
    let u:=((bitStep useMask).run n T)^[k] m
    (∀r:Reg,r≠dest bitI → u.reg r=m.reg r) ∧ u.reg (dest bitI)=(k:ℤ) ∧ Bits m u A B k useMask := by
  induction k with
  | zero=>exact ⟨fun _ _=>rfl,start,fun _ hj=>by omega,fun _ _=>rfl⟩
  | succ k ih=>
    let t:=((bitStep useMask).run n T)^[k] m
    have rt:=ih.1
    have k0:t.reg (dest bitI)=(k:ℤ):=ih.2.1
    have o:t.reg (dest outB)=(A:ℤ):=(rt _ (by decide)).trans outB0
    have i:t.reg (dest inB)=(B:ℤ):=(rt _ (by decide)).trans inB0
    have old: t.mem (cell 3 (B+k))=m.mem (cell 3 (B+k)):=ih.2.2.2 _ (fun _ _=>cell_ne_word (by decide))
    let u:=(bitStep useMask).run n T t
    have mem (q:ℤ) : u.mem q=if q=word 5 (A+k) then (if useMask then m.mem (cell 3 (B+k)) else 0) else t.mem q := by
      cases useMask <;> simp only [u,bitStep,P.run,inc,set_mem,put_mem,W_val,C_val,plus_val,V_val,lit_val,read_val,k0,o,i,←Nat.cast_add,wz_nat,cz_nat,Bool.false_eq_true,if_false,if_true,old]
    rw [Function.iterate_succ_apply']
    change (∀r:Reg,r≠dest bitI → u.reg r=_) ∧ u.reg (dest bitI)=_ ∧ Bits m u A B (k+1) useMask
    refine ⟨?_,?_,?_,?_⟩
    · intro r h;exact (by simp only [u,bitStep,P.run,inc,set_reg,if_neg h,put_reg] : u.reg r=t.reg r).trans (rt r h)
    · simp [u,bitStep,P.run,inc,k0]
    · intro j hj;rw [mem]
      by_cases eq:j=k
      · simp [eq]
      · rw [if_neg (by unfold word;push_cast;omega)]
        exact ih.2.2.1 j (by omega)
    · intro q h;rw [mem,if_neg (h k (by omega))];exact ih.2.2.2 q (fun j hj=>h j (by omega))

theorem bits_spec (n T P0 i : ℕ) (useMask : Bool) (m : Model)
    (phys0 : phys.val m=(P0:ℤ)) (ix0 : (V ix).val m=(i:ℤ)) :
    let u:=(writeBits useMask).run n T m
    Fixed m u ∧ Bits m u (P0*n) (i*n) n useMask := by
  let a:=products.run n T m
  let b:=a.set bitI 0
  obtain ⟨ma,ka,aa,ia⟩:=products_spec n T m
  have outB0:b.reg (dest outB)=((P0*n:ℕ):ℤ):=by simpa [b,a,show dest outB≠dest bitI by decide,aa,phys0,mul_comm]
  have inB0:b.reg (dest inB)=((i*n:ℕ):ℤ):=by simpa [b,a,show dest inB≠dest bitI by decide,ia,ix0,mul_comm]
  obtain ⟨rt,_,hit,keep⟩:=bit_loop n T n (P0*n) (i*n) useMask b outB0 inB0 (by simp [b])
  refine ⟨?_,?_,?_⟩
  · intro r ro ri rb
    exact (rt r rb).trans ((by simp [b,rb] : b.reg r=a.reg r).trans (ka r ro ri rb))
  · intro j hj;exact (hit j hj).trans (by simp [b,a,ma])
  · intro q h;exact (keep q h).trans (congrFun ma q)

theorem arg_frame (m u : Model) (eq : u.reg=m.reg) (a : Arg) : a.expr.val u=a.expr.val m := by cases a <;> simp [Arg.expr,eq]
theorem enc_frame (m u : Model) (eq : u.reg=m.reg) (tag:ℤ) (a : Arg) : (encoded tag a).val u=(encoded tag a).val m := by
  unfold encoded;split <;> simp [arg_frame m u eq,eq]
theorem fields_spec (n T P0 : ℕ) (m : Model) (tag:ℤ) (a b:Arg) (addr:phys.val m=(P0:ℤ)) :
    let u:=(fields tag a b).run n T m
    u.reg=m.reg ∧ ∀q,u.mem q=
      if q=word 3 P0 then (encoded tag b).val m else if q=word 2 P0 then (encoded tag a).val m else if q=word 1 P0 then tag else m.mem q := by
  let s:=m.put (word 1 P0) tag
  let t:=s.put (word 2 P0) ((encoded tag a).val m)
  have ds:phys.val s=phys.val m:=rfl
  have dt:phys.val t=phys.val m:=rfl
  have va: (encoded tag a).val s=(encoded tag a).val m:=enc_frame m s rfl tag a
  have vb: (encoded tag b).val t=(encoded tag b).val m:=enc_frame m t rfl tag b
  refine ⟨rfl,?_⟩;intro q
  simp only [fields,seqs,P.run,W_val,addr,wz_nat,lit_val]
  change ((s.put (wz 2 (phys.val s)) ((encoded tag a).val s)).put _ _).mem q=_
  rw [ds,addr,wz_nat,va]
  change (t.put (wz 3 (phys.val t)) ((encoded tag b).val t)).mem q=_
  rw [dt,addr,wz_nat,vb]
  simp [t,s]

def Flds (n : ℕ) (m : ℤ→ℤ) (p j : ℕ) (op : Gate) : Prop :=
  m (word 1 p)=opCode op ∧ m (word 2 p)=displacement op j (leftID op) ∧
  m (word 3 p)=displacement op j (rightID op) ∧ ∀k<n,m (word 5 (p*n+k))=(if (tinyMask op).contains k then 1 else 0)
def touched (n P0 : ℕ) (q:ℤ) := q=word 1 P0 ∨ q=word 2 P0 ∨ q=word 3 P0 ∨ ∃j<n,q=word 5 (P0*n+j)

theorem emit_spec (n T P0 i j : ℕ) (m : Model) (op : Gate) (tag:ℤ) (mask:Bool) (a b:Arg)
    (addr:phys.val m=(P0:ℤ)) (pos:(V ix).val m=(i:ℤ)) (gate:(V gc).val m=(j:ℤ))
    (tagOK:tag=opCode op) (aOK:(encoded tag a).val m=displacement op j (leftID op))
    (bOK:(encoded tag b).val m=displacement op j (rightID op))
    (maskOK:∀k<n,(if mask then m.mem (cell 3 (i*n+k)) else 0)=(if (tinyMask op).contains k then 1 else 0)) :
    let u:=(emit tag mask a b).run n T m
    u.reg (dest gc)=((j+1:ℕ):ℤ) ∧
    (∀r:Reg,r≠dest gc → r≠dest outB → r≠dest inB → r≠dest bitI → u.reg r=m.reg r) ∧
    Flds n u.mem P0 j op ∧ ∀q,¬touched n P0 q → u.mem q=m.mem q := by
  let s:=(fields tag a b).run n T m
  let t:=(writeBits mask).run n T s
  obtain ⟨sr,sm⟩:=fields_spec n T P0 m tag a b addr
  have ph:phys.val s=(P0:ℤ):=by simpa only [phys,plus_val,reg_val,V_val,s,sr] using addr
  have iv:(V ix).val s=(i:ℤ):=by simpa only [s,V_val,sr] using pos
  obtain ⟨kr,bits⟩:=bits_spec n T P0 i mask s ph iv
  have gm:t.reg (dest gc)=(j:ℤ):=(kr _ (by decide) (by decide) (by decide)).trans ((congrFun sr _).trans gate)
  have metadata (f:ℕ) (hf:f<4) : t.mem (word f P0)=s.mem (word f P0):=
    bits.2 _ (fun z _ eq=>by have d:=(word_inj (by omega) (by decide)).mp eq;omega)
  have on (k:ℕ) : s.mem (cell 3 (i*n+k))=m.mem (cell 3 (i*n+k)):=by
    rw [sm];simp [cell_ne_word (by decide : 1<7),cell_ne_word (by decide : 2<7),cell_ne_word (by decide : 3<7)]
  change (t.set gc _).reg _=_ ∧ _ ∧ Flds n t.mem _ _ _ ∧ _
  refine ⟨by change (t.set gc (t.reg (dest gc)+1)).reg (dest gc)=_;simp [gm],?_,⟨?_,?_,?_,?_⟩,?_⟩
  · intro r g o v b;exact (by simp [g] : (t.set gc _).reg r=t.reg r).trans ((kr r o v b).trans (congrFun sr r))
  · rw [metadata 1 (by decide),sm];simp [word_inj (by decide:1<8),tagOK]
  · rw [metadata 2 (by decide),sm];simp [word_inj (by decide:2<8),aOK]
  · rw [metadata 3 (by decide),sm];simp [bOK]
  · intro k hk;rw [bits.1 k hk,on];exact maskOK k hk
  · intro q h
    change t.mem q=m.mem q
    have sep:=not_or.mp h
    have sep':=not_or.mp sep.2
    have last:=not_or.mp sep'.2
    rw [bits.2 q (fun k hk e=>last.2 ⟨k,hk,e⟩),sm]
    simp [sep.1,sep'.1,last.1]

end StableMSR.Recovery.NativeWriter.Production.RAM

namespace StableMSR.Recovery.NativeWriter.Production.RAM
open SingleCircuit SingleRAM Relative Relative.Machine Compiler OracleQueries
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

abbrev Mem := ℤ→ℤ
def Filled (n p : ℕ) (m : Mem) (g : Gates) := ∀j<g.size,Flds n m (p+j) j (gateAt g j)
structure Protected (n p : ℕ) (base m : Mem) : Prop where
  scene : ∀q:ℕ,m q=base q
  old : ∀a<p,∀j op,Flds n base a j op → Flds n m a j op
  dirs : ∀a, m (word 4 a)=base (word 4 a) ∧ m (word 6 a)=base (word 6 a)
  source : ∀f<4,∀a,m (cell f a)=base (cell f a)

theorem Protected.refl (n p : ℕ) (m : Mem) : Protected n p m m :=
  ⟨fun _=>rfl,fun _ _ _ _ h=>h,fun _=>⟨rfl,rfl⟩,fun _ _ _=>rfl⟩

theorem fld_transfer {n a j : ℕ} {m l : Mem} {op : Gate}
    (h : ∀q,touched n a q → l q=m q) (o : Flds n m a j op) : Flds n l a j op :=
  ⟨(h _ (Or.inl rfl)).trans o.1,(h _ (Or.inr (Or.inl rfl))).trans o.2.1,
    (h _ (Or.inr (Or.inr (Or.inl rfl)))).trans o.2.2.1,
    fun k hk=>(h _ (Or.inr (Or.inr (Or.inr ⟨k,hk,rfl⟩)))).trans (o.2.2.2 k hk)⟩

theorem gate_disjoint {n a b : ℕ} {q : ℤ} (ab:a<b) (u:touched n a q) : ¬touched n b q := by
  have sep:=Nat.mul_le_mul_right n (show a+1≤b by omega)
  rw [Nat.add_mul,Nat.one_mul] at sep
  unfold touched at *
  rcases u with h|h|h|⟨k,hk,h⟩ <;> subst q <;> rintro (e|e|e|⟨l,hl,e⟩) <;> unfold word at e <;> push_cast at e <;> omega

theorem untouched_cell (n a f i : ℕ) : ¬touched n a (cell f i) := by
  unfold touched;simp [cell_ne_word (by decide:1<7),cell_ne_word (by decide:2<7),cell_ne_word (by decide:3<7),cell_ne_word (by decide:5<7)]
theorem untouched_dir (n a f i : ℕ) (hf:f=4 ∨ f=6) : ¬touched n a (word f i) := by
  rcases hf with rfl|rfl <;> simp [touched,word_inj (by decide:4<8),word_inj (by decide:6<8)]
theorem untouched_scene (n a i : ℕ) : ¬touched n a (i:ℤ) := by
  unfold touched word
  push_neg
  exact ⟨by omega,by omega,by omega,fun k _=>by omega⟩

theorem Protected.gate {n p a : ℕ} {base m l : Mem} (fr:Protected n p base m) (le:p≤a)
    (same:∀q,¬touched n a q → l q=m q) : Protected n p base l := by
  exact ⟨fun k=>(same _ (untouched_scene _ _ _)).trans (fr.scene k),
    fun b h j op old=>fld_transfer (fun q H=>same q (gate_disjoint (by omega) H)) (fr.old b h j op old),
    fun b=>⟨(same _ (untouched_dir _ _ _ _ (Or.inl rfl))).trans (fr.dirs b).1,
      (same _ (untouched_dir _ _ _ _ (Or.inr rfl))).trans (fr.dirs b).2⟩,
    fun f h i=>(same _ (untouched_cell _ _ _ _)).trans (fr.source f h i)⟩

theorem Filled.push {n p : ℕ} {m l : Mem} {g : Gates} {op : Gate} (f : Filled n p m g)
    (hit : Flds n l (p+g.size) g.size op) (same:∀q,¬touched n (p+g.size) q→l q=m q) :
    Filled n p l (g.push op) := by
  intro j hj
  by_cases eq:j=g.size
  · subst j;simpa [gateAt,Array.getElem?_push] using hit
  · have lt:j<g.size:=by simpa using (show j<g.size from by simp at hj;omega)
    have pre:=fld_transfer (fun q H=>same q (gate_disjoint (by omega:p+j<p+g.size) H)) (f j lt)
    simpa [gateAt,Array.getElem?_push,eq,lt] using pre

theorem Protected.memo {n p i : ℕ} {base m : Mem} (fr:Protected n p base m) (z:ℤ) :
    Protected n p base (Function.update m (cell 4 i) z) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro q;rw [Function.update_of_ne (by unfold cell word;omega)];exact fr.scene q
  · intro a ha j op o
    apply fld_transfer _ (fr.old a ha j op o)
    intro q H;apply Function.update_of_ne
    rintro rfl;exact untouched_cell _ _ _ _ H
  · intro a
    simp only [Function.update_of_ne (word_ne_cell (by decide:4<7)),Function.update_of_ne (word_ne_cell (by decide:6<7))]
    exact fr.dirs a
  · intro f hf a
    rw [Function.update_of_ne (by rw [ne_eq,cell_inj (by omega) (by decide)];omega)]
    exact fr.source f hf a

theorem Filled.memo {n p i : ℕ} {m : Mem} {g:Gates} (f:Filled n p m g) (z:ℤ) :
    Filled n p (Function.update m (cell 4 i) z) g := by
  intro j hj;apply fld_transfer _ (f j hj)
  intro q H;apply Function.update_of_ne
  rintro rfl;exact untouched_cell _ _ _ _ H

structure Core (n p i : ℕ) (base : Mem) (m : Model) (g : Gates) (memo : Array ℕ) : Prop where
  safe : Protected n p base m.mem
  gates : Filled n p m.mem g
  offset : m.reg 4=(p:ℤ)
  index : (V ix).val m=(i:ℤ)
  size : (V gc).val m=(g.size:ℤ)
  refs : ∀k (hk:k < memo.size),m.mem (cell 4 k)=(memo[k]:ℤ)

theorem Core.emit {n T p i : ℕ} {base : Mem} {m : Model} {g : Gates} {memo : Array ℕ}
    (co:Core n p i base m g memo) (op:Gate) (tag:ℤ) (mask:Bool) (a b:Arg)
    (ht:tag=opCode op) (ha:(encoded tag a).val m=displacement op g.size (leftID op))
    (hb:(encoded tag b).val m=displacement op g.size (rightID op))
    (hm:∀k<n,(if mask then m.mem (cell 3 (i*n+k)) else 0)=(if (tinyMask op).contains k then 1 else 0)) :
    let u:=(RAM.emit tag mask a b).run n T m
    Core n p i base u (g.push op) memo ∧ u.reg (dest tail)=m.reg (dest tail) ∧ u.reg (dest refV)=m.reg (dest refV) := by
  have addr : phys.val m=((p+g.size:ℕ):ℤ):=by simp only [phys,plus_val,reg_val,co.offset,co.size,Nat.cast_add]
  obtain ⟨sz,reg,hit,keep⟩:=emit_spec n T _ i g.size m op tag mask a b addr co.index co.size ht ha hb hm
  exact ⟨⟨co.safe.gate (by omega) keep,co.gates.push hit keep,
    (reg 4 (by decide) (by decide) (by decide) (by decide)).trans co.offset,
    (reg _ (by decide) (by decide) (by decide) (by decide)).trans co.index,by simpa using sz,
    fun k hk=>(keep _ (untouched_cell _ _ _ _)).trans (co.refs k hk)⟩,
    reg _ (by decide) (by decide) (by decide) (by decide),reg _ (by decide) (by decide) (by decide) (by decide)⟩

theorem Core.set {n p i : ℕ} {base : Mem} {m : Model} {g : Gates} {memo : Array ℕ}
    (co:Core n p i base m g memo) (v : Var) (z:ℤ) (hg:dest gc≠dest v) (hi:dest ix≠dest v) :
    Core n p i base (m.set v z) g memo := by
  exact ⟨co.safe,co.gates,(Function.update_of_ne (by intro h;have:=congrArg Fin.val h;dsimp [dest] at this;omega : (4:Reg)≠dest v) ..).trans co.offset,
    (Function.update_of_ne hi ..).trans co.index,(Function.update_of_ne hg ..).trans co.size,co.refs⟩

end StableMSR.Recovery.NativeWriter.Production.RAM

namespace StableMSR.Recovery.NativeWriter.Production.RAM
open SingleCircuit SingleRAM Relative Relative.Machine Compiler OracleQueries TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

def pin (v:E) := P.seq (.put (C 4 (plus (V ix) (.lit 1))) v) (inc ix)
def getRef (e:E) := P.test e (V ix) (.set refV (.read (C 4 e))) (.set refV (.lit 1))
def operand := E.read (C 2 (V ix))
def opcode := E.read (C 1 (V ix))
def tailLast := P.set tail Arg.previous.expr
def zeroTail := P.set tail (.lit 0)
def literalBody := seqs [emit 0 true .zero .zero,emit 1 false .acc .previous,tailLast,pin (.lit 1)]
def childBody := seqs [getRef operand,emit 1 false .acc .ref,tailLast,pin (.lit 1)]
def unionBody := seqs [getRef operand,emit 2 false .ref .acc,pin Arg.previous.expr,zeroTail]
def saveBody := seqs [pin (V tail),zeroTail]
def eventCode := P.test opcode (.lit 0) literalBody
   (.test opcode (.lit 1) childBody (.test opcode (.lit 2) unionBody saveBody))

end StableMSR.Recovery.NativeWriter.Production.RAM

namespace StableMSR.Recovery.NativeWriter.Production.RAM
open SingleCircuit SingleRAM Relative Relative.Machine Compiler OracleQueries TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

theorem Core.pin {n T p i : ℕ} {base : Mem} {m : Model} {g : Gates} {memo : Array ℕ}
    (co:Core n p i base m g memo) (len:memo.size=i+1) (e:E) (v:ℕ) (hv:e.val m=(v:ℤ)) :
    let t:=(RAM.pin e).run n T m
    Core n p (i+1) base t g (memo.push v) ∧ t.reg (dest tail)=m.reg (dest tail) := by
  let q:=cell 4 (i+1)
  let u:=m.put q (v:ℤ)
  let t:=u.set ix ((i+1:ℕ):ℤ)
  have eq:(RAM.pin e).run n T m=t:=by
    simp only [RAM.pin,inc,P.run,C_val,plus_val,co.index,lit_val,hv,V_val,put_reg]
    change (m.put (cz 4 ((i:ℤ)+1)) (v:ℤ)).set ix ((V ix).val m+1)=_
    rw [co.index,←Nat.cast_one (R:=ℤ),←Nat.cast_add,cz_nat]
  rw [eq]
  refine ⟨⟨co.safe.memo _,co.gates.memo _,?_,?_,?_,?_⟩,?_⟩
  · exact co.offset
  · simp [t]
  · exact co.size
  · intro k hk
    by_cases same:k=memo.size
    · subst k;simp [t,u,q,Array.getElem_push,len]
    · have old:k < memo.size:=by simp at hk;omega
      simp only [t,u,set_mem,put_mem,q,cell_inj (by decide:4<8) (by decide:4<8),true_and,
        if_neg (show k≠i+1 by omega),Array.getElem_push,dif_pos old]
      exact co.refs k old
  · rfl

end StableMSR.Recovery.NativeWriter.Production.RAM

namespace StableMSR.Recovery.NativeWriter.Production.RAM
open SingleCircuit SingleRAM Relative Relative.Machine Compiler OracleQueries TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

theorem Core.getRef {n T p i : ℕ} {base : Mem} {m : Model} {st : State}
    (co:Core n p i base m st.gates st.memo) (len:st.memo.size=i+1) (e:E) (k:ℕ) (hv:e.val m=(k:ℤ)) :
    let t:=(RAM.getRef e).run n T m
    Core n p i base t st.gates st.memo ∧ t.reg (dest refV)=(resolve st k:ℤ) ∧ t.reg (dest tail)=m.reg (dest tail) := by
  unfold RAM.getRef;dsimp only [P.run];rw [hv,co.index]
  by_cases hk:k ≤ i
  · rw [if_pos ((show (k:ℤ)≤(i:ℤ) by exact_mod_cast hk))]
    have lt:k < st.memo.size:=by omega
    refine ⟨co.set refV _ (by decide) (by decide),?_,rfl⟩
    simp [hv,resolve,lt,co.refs k lt]
  · rw [if_neg ((show ¬(k:ℤ)≤(i:ℤ) by exact_mod_cast hk))]
    exact ⟨co.set refV _ (by decide) (by decide),by simp [resolve,Array.getElem?_eq_none (by omega:st.memo.size≤k)],rfl⟩

end StableMSR.Recovery.NativeWriter.Production.RAM

namespace StableMSR.Recovery.NativeWriter.Production.RAM
open SingleCircuit SingleRAM Relative Relative.Machine Compiler OracleQueries TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

theorem Core.binary {n T p i : ℕ} {base : Mem} {m : Model} {g : Gates} {memo : Array ℕ}
    (co:Core n p i base m g memo) (choice:Bool) (l r:Arg) (L R:ℕ)
    (hl:l.expr.val m=(L:ℤ)) (hr:r.expr.val m=(R:ℤ)) :
    let op:=if choice then Gate.either L R else Gate.both L R
    let tag:ℤ:=if choice then 2 else 1
    let u:=(RAM.emit tag false l r).run n T m
    Core n p i base u (g.push op) memo ∧ u.reg (dest tail)=m.reg (dest tail) ∧ u.reg (dest refV)=m.reg (dest refV) := by
  cases choice
  · apply co.emit (.both L R) 1 false l r rfl <;> simp [encoded,displacement,opCode,leftID,rightID,tinyMask,hl,hr,co.size]
  · apply co.emit (.either L R) 2 false l r rfl <;> simp [encoded,displacement,opCode,leftID,rightID,tinyMask,hl,hr,co.size]
theorem Core.atom {n T p i : ℕ} {base : Mem} {m : Model} {g : Gates} {memo : Array ℕ}
    (co:Core n p i base m g memo) (pts:List ℕ) (mask:Bool)
    (hm:∀k<n,(if mask then m.mem (cell 3 (i*n+k)) else 0)=(if pts.contains k then 1 else 0)) :
    let u:=(RAM.emit 0 mask .zero .zero).run n T m
    Core n p i base u (g.push (.atom pts)) memo ∧ u.reg (dest tail)=m.reg (dest tail) ∧ u.reg (dest refV)=m.reg (dest refV) :=
  co.emit (.atom pts) 0 mask .zero .zero rfl rfl rfl hm

theorem last_value {g:Gates} {op:Gate} {m:Model} (h:(V gc).val m=((g.push op).size:ℤ)) : Arg.previous.expr.val m=(g.size:ℤ) := by
  change (V gc).val m-1=_;rw [h];simp
theorem last_set {n T p i : ℕ} {base : Mem} {m : Model} {g : Gates} {memo : Array ℕ} {op : Gate}
    (co:Core n p i base m (g.push op) memo) :
    let t:=tailLast.run n T m
    Core n p i base t (g.push op) memo ∧ t.reg (dest tail)=(g.size:ℤ) :=
  ⟨co.set tail _ (by decide) (by decide),by simpa [tailLast,P.run] using last_value co.size⟩

end StableMSR.Recovery.NativeWriter.Production.RAM

namespace StableMSR.Recovery.NativeWriter.Production.RAM
open SingleCircuit SingleRAM Relative Relative.Machine Compiler OracleQueries TightLanguage
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

theorem run_event (n T p i : ℕ) (base : Mem) (m : Model) (st : State) (e : Event)
    (co:Core n p i base m st.gates st.memo) (len:st.memo.size=i+1) (acc:m.reg (dest tail)=(st.tail:ℤ))
    (kind:base (cell 1 i)=e.tag) (arg:base (cell 2 i)=e.arg)
    (mask:∀pts,e=.mask pts → ∀k<n,base (cell 3 (i*n+k))=e.bit k) :
    let t:=eventCode.run n T m
    Core n p (i+1) base t (step st e).gates (step st e).memo ∧ t.reg (dest tail)=((step st e).tail:ℤ) := by
  have tag:opcode.val m=e.tag:=by simp [opcode,co.index,co.safe.source 1 (by decide) i,kind]
  have get:operand.val m=e.arg:=by simp [operand,co.index,co.safe.source 2 (by decide) i,arg]
  cases e with
  | mask pts=>
    have eq:eventCode.run n T m=literalBody.run n T m:=by simp [eventCode,P.run,tag,Event.tag]
    rw [eq]
    obtain ⟨a,keep,_⟩:=co.atom (T:=T) pts true (fun k hk=>by
      simpa only [if_true,Bool.true_eq,co.safe.source 3 (by decide) _,Event.bit] using mask pts rfl k hk)
    obtain ⟨b,_,_⟩:=a.binary (T:=T) false .acc .previous st.tail st.gates.size (keep.trans acc) (last_value a.size)
    obtain ⟨c,tail'⟩:=last_set (T:=T) b
    obtain ⟨d,keep'⟩:=c.pin (T:=T) len (.lit 1) 1 rfl
    exact ⟨d,keep'.trans tail'⟩
  | child k=>
    have eq:eventCode.run n T m=childBody.run n T m:=by simp [eventCode,P.run,tag,Event.tag]
    rw [eq]
    obtain ⟨a,ref',keep⟩:=co.getRef (T:=T) len operand k get
    obtain ⟨b,_,_⟩:=a.binary (T:=T) false .acc .ref st.tail (resolve st k) (keep.trans acc) ref'
    obtain ⟨c,tail'⟩:=last_set (T:=T) b
    obtain ⟨d,keep'⟩:=c.pin (T:=T) len (.lit 1) 1 rfl
    exact ⟨d,keep'.trans tail'⟩
  | join k=>
    have eq:eventCode.run n T m=unionBody.run n T m:=by simp [eventCode,P.run,tag,Event.tag]
    rw [eq]
    obtain ⟨a,ref',keep⟩:=co.getRef (T:=T) len operand k get
    obtain ⟨b,_,_⟩:=a.binary (T:=T) true .ref .acc (resolve st k) st.tail ref' (keep.trans acc)
    obtain ⟨c,_⟩:=b.pin (T:=T) len Arg.previous.expr st.gates.size (last_value b.size)
    exact ⟨c.set tail 0 (by decide) (by decide),rfl⟩
  | save=>
    have eq:eventCode.run n T m=saveBody.run n T m:=by simp [eventCode,P.run,tag,Event.tag]
    rw [eq]
    obtain ⟨a,_⟩:=co.pin (T:=T) len (V tail) st.tail acc
    exact ⟨a.set tail 0 (by decide) (by decide),rfl⟩

end StableMSR.Recovery.NativeWriter.Production.RAM

namespace StableMSR.Recovery.NativeWriter.Production.RAM
open SingleCircuit SingleRAM Relative Relative.Machine Compiler OracleQueries
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

def clear := seqs [.set gc (.lit 0),.set ix (.lit 0),zeroTail,.put (C 4 (.lit 0)) (.lit 1)]
def seed := seqs [clear,emit 0 false .zero .zero,emit (-1) false .zero .zero]
def exitWord := E.read (C 0 (.lit 1))
def listPass := P.rep .events eventCode
def directoryCode (token:E) := P.seq (.put (W 4 (.reg 3)) token) (.put (W 6 (.reg 3)) (V gc))
def live := seqs [seed,listPass,getRef exitWord,directoryCode (V refV)]
def empty := P.seq (.set gc (.lit 0)) (directoryCode exitWord)
def program := P.test exitWord (.lit (-1)) empty live

theorem seed_ok (n T p : ℕ) (m : Model) (offset:m.reg 4=(p:ℤ)) :
    let a:=seed.run n T m
    Core n p 0 m.mem a initial.gates initial.memo ∧ a.reg (dest tail)=0 := by
  let c:=clear.run n T m
  have cm:c.mem=Function.update m.mem (cell 4 0) 1:=rfl
  have co:Core n p 0 m.mem c #[] #[1]:=by
    refine ⟨cm ▸ (Protected.refl n p m.mem).memo _,fun _ hj=>by simp at hj,offset,rfl,rfl,?_⟩
    intro k hk
    have bound:k<1:=hk
    have eq:k=0:=by omega
    subst k;rw [cm];simp
  obtain ⟨a,ta,_⟩:=co.atom (T:=T) [] false (fun _ _=>rfl)
  obtain ⟨b,tb,_⟩:=a.emit (T:=T) .stop (-1) false .zero .zero rfl rfl rfl (fun _ _=>rfl)
  exact ⟨b,tb.trans ta⟩

theorem events_ok (n p : ℕ) (a : Script) (base : Mem) (m : Model) (buf:Stored n base a)
    (co:Core n p 0 base m initial.gates initial.memo) (tail0:m.reg (dest tail)=0) :
    let t:=listPass.run n a.events.length m
    Core n p a.events.length base t (play a.events).gates (play a.events).memo ∧ t.reg (dest tail)=((play a.events).tail:ℤ) := by
  have loop (k : ℕ) (hk:k≤a.events.length) :
      let t:=(eventCode.run n a.events.length)^[k] m
      let v:=play (a.events.take k)
      Core n p k base t v.gates v.memo ∧ t.reg (dest tail)=(v.tail:ℤ) := by
    induction k with
    | zero=>exact ⟨co,tail0⟩
    | succ k ih=>
      have lt:k<a.events.length:=by omega
      have old:=ih (by omega)
      have info:=buf.2.2 k lt
      have sz:(play (a.events.take k)).memo.size=k+1:=by simp [play_size, Nat.min_eq_left (by omega:k≤a.events.length)]
      rw [Function.iterate_succ_apply',List.take_succ_eq_append_getElem lt,play_append]
      exact run_event n a.events.length p k base _ _ _ old.1 sz old.2 info.1 info.2.1 info.2.2
  simpa [listPass,P.run,Axis.len] using loop a.events.length (by rfl)

structure Outcome (n r p : ℕ) (base : Mem) (m : Model) (a : Packet) : Prop where
  len : (V gc).val m=(a.gates.size:ℤ)
  scene : ∀q:ℕ,m.mem q=base q
  gates : Filled n p m.mem a.gates
  here : m.mem (word 4 r)=a.token ∧ m.mem (word 6 r)=(a.gates.size:ℤ)
  before : ∀q<p,∀j op,Flds n base q j op → Flds n m.mem q j op
  dirs : ∀q<r,m.mem (word 4 q)=base (word 4 q) ∧ m.mem (word 6 q)=base (word 6 q)

theorem write_directory (n T r p : ℕ) (base : Mem) (m : Model) (g : Gates) (tok:ℤ) (e:E)
    (fr:Protected n p base m.mem) (gates:Filled n p m.mem g) (sz:(V gc).val m=(g.size:ℤ))
    (slot:m.reg 3=(r:ℤ)) (value:e.val m=tok) :
    Outcome n r p base ((directoryCode e).run n T m) ⟨g,tok⟩ := by
  let t:=(directoryCode e).run n T m
  have mem (q:ℤ):t.mem q=if q=word 6 r then (g.size:ℤ) else if q=word 4 r then tok else m.mem q := by
    simp only [t,directoryCode,P.run,W_val,reg_val,put_reg,slot,wz_nat,put_mem,value,V_val]
    rw [show m.reg (dest gc)=(g.size:ℤ) from sz]
  have preserve {q:ℤ} {a:ℕ} (h:touched n a q) : t.mem q=m.mem q := by
    have k6:q≠word 6 r:=by rintro rfl;exact untouched_dir n a 6 r (Or.inr rfl) h
    have k4:q≠word 4 r:=by rintro rfl;exact untouched_dir n a 4 r (Or.inl rfl) h
    rw [mem,if_neg k6,if_neg k4]
  refine ⟨sz,?_,fun j hj=>fld_transfer (fun _ h=>preserve h) (gates j hj),?_,
    fun a h j op o=>fld_transfer (fun _ k=>preserve k) (fr.old a h j op o),?_⟩
  · intro q;rw [mem,if_neg (by unfold word;omega),if_neg (by unfold word;omega),fr.scene]
  · constructor <;> rw [mem] <;> simp [word_inj (by decide:4<8) (by decide:6<8)]
  · intro q h
    have ne:q≠r:=Nat.ne_of_lt h
    constructor <;> rw [mem] <;> simp [word_inj (by decide:4<8),word_inj (by decide:6<8),ne,fr.dirs q]

theorem program_ok (n r p : ℕ) (m : Model) (a : Script) (buf:Stored n m.mem a)
    (slot:m.reg 3=(r:ℤ)) (offset:m.reg 4=(p:ℤ)) :
    Outcome n r p m.mem (program.run n a.events.length m) a.packet := by
  have e:exitWord.val m=a.exit:=buf.2.1
  unfold program;dsimp only [P.run];rw [e];change Outcome _ _ _ _ (if a.exit≤-1 then _ else _) _
  by_cases neg:a.exit<0
  · rw [if_pos (by omega:a.exit≤-1)]
    rw [Script.packet,if_pos neg]
    let u:=m.set gc 0
    exact write_directory n a.events.length r p m.mem u #[] a.exit exitWord (Protected.refl ..) (fun j hj=>by simp at hj) rfl slot e
  · rw [if_neg (by omega:¬a.exit≤-1),Script.packet,if_neg neg]
    let T:=a.events.length
    let u:=seed.run n T m
    let v:=listPass.run n T u
    let y:=(getRef exitWord).run n T v
    obtain ⟨ready,zero⟩:=seed_ok n T p m offset
    obtain ⟨endCo,acc⟩:=events_ok n p a m.mem u buf ready zero
    have ve:exitWord.val v=(a.exit.toNat:ℤ):=by
      change v.mem (cell 0 1)=_;rw [endCo.safe.source 0 (by decide) 1,buf.2.1,Int.toNat_of_nonneg (by omega)]
    obtain ⟨last,ref',_⟩:=endCo.getRef (T:=T) (play_size _) exitWord a.exit.toNat ve
    have vslot:y.reg 3=(r:ℤ):=by
      exact ((getRef exitWord).fixed n T v 3 (by decide)).trans ((listPass.fixed n T u 3 (by decide)).trans ((seed.fixed n T m 3 (by decide)).trans slot))
    exact write_directory n T r p m.mem y _ _ (V refV) last.safe last.gates last.size vslot ref'

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

theorem program_time (n T : ℕ) : program.time n T≤program.weight*(1+n)*(1+T) := by
  have h:=time_bound program n T true true (by decide)
  simpa [fac,Nat.mul_assoc] using h

end StableMSR.Recovery.NativeWriter.Production.RAM

namespace StableMSR.Recovery.NativeWriter.Production.RAM
open Compiler OracleQueries Relative Relative.Machine SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000

def setup : List Op := [.pointerConst 15 (cell 0 0),.integerLoad 15 15]
def decoder := Cmd.seq (line setup) (.seq (program.code 32) (.atom (.pointerCopy 7 (dest gc).val)))

theorem native_decode :  ∃ (A : ℕ) (cmd : Cmd),∀(x : World) (s : Store) (r p : ℕ) (a : Script),
    Ready x s → s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → Stored x.n s.imem a →
    ∃t z, Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+a.events.length) ∧
      Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧ t.ptrs 7=(a.packet.gates.size:ℤ) ∧
      (∀j<a.packet.gates.size, Record x.n t (p+j) j (gateAt a.packet.gates j)) ∧
      DirAt t r (a.packet.token,a.packet.gates.size) ∧
      (∀q<p,∀j op,Record x.n s q j op → Record x.n t q j op) ∧
      ∀q<r,∀v,DirAt s q v → DirAt t q v 
 := by
  refine ⟨program.weight+3,decoder,?_⟩
  intro x s r p a ready slot offset buf
  let T:=a.events.length
  let b:=perform x.dist s setup
  have reg (j:ℕ) (hj:j<15) : b.ptrs j=s.ptrs j:=by
    simp [b,setup,perform,Op.eval,Function.update_of_ne (by omega:j≠15)]
  have cnt:b.ptrs 15=(T:ℤ):=by simpa [b,setup,perform,Op.eval,T] using buf.1
  have fit:Fit x.n T b:=⟨(reg 0 (by decide)).trans (ready.1 .points),cnt⟩
  obtain ⟨u,z,go,cost,sim⟩:=execute x.dist T program 32 (by decide) b fit
  have modelled:=program_ok x.n r p (model b) a buf ((reg 3 (by decide)).trans slot) ((reg 4 (by decide)).trans offset)
  rw [←sim.1] at modelled
  let t:=(Op.pointerCopy 7 (dest gc).val).eval x.dist u
  have low (j:Reg) (hj:j.val<7) : t.ptrs j.val=s.ptrs j.val:=by
    have ru:=congrArg (fun m:Model=>m.reg j) sim.1
    exact (Function.update_of_ne (by omega:j.val≠7) ..).trans (ru.trans ((program.fixed x.n T _ _ (by omega)).trans (reg j.val (by omega))))
  refine ⟨t,_,.seq (line_exec x.dist s _) (.seq go (.atom _ _)),?_,⟨?_,?_⟩,?_,?_,modelled.gates,modelled.here,modelled.before,?_⟩
  · have bound:=program_time x.n T
    have pos:1≤(1+x.n)*(1+T):=by nlinarith
    change 2+(z+1)≤_
    have h:z≤program.weight*(1+x.n)*(1+T):=cost.trans bound
    dsimp only [T] at *
    rw [Nat.add_mul,Nat.add_mul]
    nlinarith
  · intro ax;cases ax <;> first
      | exact (low 0 (by decide)).trans (ready.1 .points)
      | exact (low 1 (by decide)).trans (ready.1 .blocks)
      | exact (low 2 (by decide)).trans (ready.1 .rows)
  · intro q;exact (modelled.scene q).trans (ready.2 q)
  · intro j hj
    have small:j<7:=by simp at hj;omega
    exact low ⟨j,by omega⟩ small
  · change Function.update u.ptrs 7 (u.ptrs (dest gc).val) 7=_
    rw [Function.update_self];exact modelled.len
  · intro q h v dir
    exact ⟨(modelled.dirs q h).1.trans dir.1,(modelled.dirs q h).2.trans dir.2⟩

end StableMSR.Recovery.NativeWriter.Production.RAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit
theorem solution :
  ∃ (A : ℕ) (cmd : Cmd),∀(x : World) (s : Store) (r p : ℕ) (a : Script),
    Ready x s → s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → Stored x.n s.imem a →
    ∃t z, Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+a.events.length) ∧
      Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧ t.ptrs 7=(a.packet.gates.size:ℤ) ∧
      (∀j<a.packet.gates.size, Record x.n t (p+j) j (gateAt a.packet.gates j)) ∧
      DirAt t r (a.packet.token,a.packet.gates.size) ∧
      (∀q<p,∀j op,Record x.n s q j op → Record x.n t q j op) ∧
      ∀q<r,∀v,DirAt s q v → DirAt t q v := StableMSR.Recovery.NativeWriter.Production.RAM.native_decode
