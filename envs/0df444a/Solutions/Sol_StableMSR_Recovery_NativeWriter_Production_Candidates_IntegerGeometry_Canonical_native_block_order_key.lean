-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.native_block_order_key
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:17:26.827849+00:00
-- url     : https://prove2.me/submissions/6c58272f-9755-4c2c-8258-f1fdf5062476

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
open Compiler OracleQueries Relative.Machine
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

inductive Field where | ptr (j:ℕ) | real (j:ℕ) | mem | imem | queries
def Field.Ty : Field→Type | .ptr _=>ℤ | .real _=>ℝ | .mem=>ℤ→ℝ | .imem=>ℤ→ℤ | .queries=>ℕ
def Field.val (s:Store) : (f:Field)→f.Ty
  | .ptr j=>s.ptrs j | .real j=>s.regs j | .mem=>s.mem | .imem=>s.imem | .queries=>s.queries
def safeOp (f:Field) (o:Op) : Bool := match f,o with
  | .ptr j,.pointerConst i _ | .ptr j,.pointerCopy i _ | .ptr j,.pointerInc i | .ptr j,.pointerDec i |
    .ptr j,.pointerAdd i _ _ | .ptr j,.pointerSub i _ _ | .ptr j,.integerLoad i _=>j != i
  | .real j,.realConst i _ | .real j,.realAdd i _ _ | .real j,.realSub i _ _ | .real j,.realMul i _ _ |
    .real j,.realDiv i _ _ | .real j,.realLoad i _ | .real j,.pointerReal i _ | .real j,.distance i _ _=>j != i
  | .mem,.realStore .. | .imem,.integerStore .. | .queries,.distance ..=>false
  | _,_=>true
def safe (f:Field) : Cmd→Bool
  | .skip=>true | .atom o=>safeOp f o | .seq a b | .ite _ a b=>safe f a && safe f b | .whileDo _ a=>safe f a

theorem preserves {n:ℕ} {d:Fin n→Fin n→ℝ} {c:Cmd} {s t:Store} {z:ℕ} (ex:Executes d c s t z) (f:Field) (h:safe f c=true) :
    f.val t=f.val s := by
  induction ex with
  | skip=>rfl
  | atom op s=>
    cases f <;> cases op <;> simp_all [safe,safeOp,Field.val,Op.eval,Function.update_apply] <;> rfl
  | seq _ _ ih jh=>obtain ⟨a,b⟩:=Bool.and_eq_true_iff.mp h;exact (jh b).trans (ih a)
  | ite_true _ _ ih=>exact ih (Bool.and_eq_true_iff.mp h).1
  | ite_false _ _ ih=>exact ih (Bool.and_eq_true_iff.mp h).2
  | while_false=>rfl
  | while_true _ _ _ ih jh=>exact (jh h).trans (ih h)


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.LexMask
set_option autoImplicit false

/-- List of the marked positions, in increasing order. -/
def indices : List Bool → List ℕ
  | []=>[]
  | b::bs=>let rest:=(indices bs).map Nat.succ
           if b then 0::rest else rest
/-- Preorder number of the marked positions among all increasing lists in the same interval. -/
def prepend (b:Bool) (p k:ℕ) := if b then k+1 else if k=0 then 0 else p+k
def rank : List Bool → ℕ
  | []=>0
  | b::bs=>prepend b (2^bs.length) (rank bs)
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.LexMask

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.LexMask
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem rank_bound (bs:List Bool) : rank bs<2^bs.length:=by
  induction bs with
  | nil=>decide
  | cons b bs ih=>
    simp only [rank,List.length_cons,pow_succ]
    have :=Nat.two_pow_pos bs.length
    cases b <;> simp [prepend] <;> (try split_ifs) <;> omega

theorem rank_zero (bs:List Bool) : rank bs=0 ↔ indices bs=[]:=by
  induction bs with
  | nil=>simp [rank,indices]
  | cons b bs ih=>
    have hp:=Nat.two_pow_pos bs.length
    cases b
    · simp only [rank,prepend,Bool.false_eq_true,if_false,indices,List.map_eq_nil_iff]
      by_cases h:rank bs=0 <;> simp [h,←ih] <;> omega
    · simp [rank,prepend,indices]

theorem map_succ_lt (a b:List ℕ) : a.map Nat.succ < b.map Nat.succ ↔ a<b:=by
  induction a generalizing b with
  | nil=>cases b <;> simp
  | cons x xs ih=>
    cases b with
    | nil=>simp
    | cons y ys=>simp [List.cons_lt_cons_iff,ih]

theorem rank_lt {a b:List Bool} (len:a.length=b.length) :
    rank a<rank b ↔ indices a < indices b:=by
  induction a generalizing b with
  | nil=>cases b <;> simp_all
  | cons x xs ih=>
    cases b with
    | nil=>simp at len
    | cons y ys=>
      have h:xs.length=ys.length:=by simpa using len
      have order:=ih h
      have hx:=rank_bound xs
      have hy:=rank_bound ys
      rw [h] at hx
      have zx:=rank_zero xs
      have zy:=rank_zero ys
      have hp:=Nat.two_pow_pos ys.length
      cases x <;> cases y
      · simp only [rank,prepend,indices,Bool.false_eq_true,if_false,map_succ_lt,h,←order]
        by_cases a:rank xs=0 <;> by_cases b:rank ys=0 <;> simp [a,b] <;> omega
      · simp only [rank,prepend,indices,Bool.false_eq_true,if_false,if_true,h]
        by_cases z:rank xs=0
        · simp [z,zx.mp z]
        · obtain ⟨k,ks,e⟩:=List.exists_cons_of_ne_nil (fun e=>z (zx.mpr e))
          simp [z,e,List.cons_lt_cons_iff];omega
      · simp only [rank,prepend,indices,Bool.false_eq_true,if_false,if_true,h]
        by_cases z:rank ys=0
        · simp [z,zy.mp z]
        · obtain ⟨k,ks,e⟩:=List.exists_cons_of_ne_nil (fun e=>z (zy.mpr e))
          simp [z,e,List.cons_lt_cons_iff];omega
      · simpa [rank,prepend,indices,List.cons_lt_cons_iff,map_succ_lt] using order

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.LexMask

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.LexMask
open Compiler Relative.Machine
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

def beginOps : List Op := [.pointerConst 41 1,.pointerCopy 42 0,.pointerAdd 43 30 0,.pointerConst 44 0,.pointerConst 45 1]
def fetchOps : List Op := [.pointerDec 43,.integerLoad 46 43,.pointerDec 42]
def yesOp : Op := .pointerInc 44
def noOp : Op := .pointerAdd 44 45 44
def twice : Op := .pointerAdd 45 45 45
def right := Cmd.ite (.pointerLE 41 44) (.atom noOp) .skip
def branch := Cmd.ite (.pointerLE 41 46) (.atom yesOp) right
def advance := Cmd.seq (line fetchOps) (.seq branch (.atom twice))
def loop := Cmd.whileDo (.pointerLE 41 42) advance
def program := Cmd.seq (line beginOps) loop

structure At (base:ℤ) (pre suf:List Bool) (s:Store) : Prop where
  one : s.ptrs 41=1
  remain : s.ptrs 42=(pre.length:ℤ)
  cursor : s.ptrs 43=base+(pre.length:ℤ)
  value : s.ptrs 44=(rank suf:ℤ)
  power : s.ptrs 45=(2^suf.length:ℕ)
  present : ∀j (h:j<pre.length),s.imem (base+(j:ℤ))=(if pre[j] then 1 else 0)

theorem tick {n:ℕ} (d:Fin n→Fin n→ℝ) (base:ℤ) (xs ys:List Bool) (b:Bool) (s:Store) (h:At base (xs++[b]) ys s) :
    ∃t z,Executes d advance s t z ∧ z≤9 ∧ At base xs (b::ys) t:=by
  let u:=perform d s fetchOps
  have hit:=h.present xs.length (by simp)
  simp only [List.getElem_append_right (show xs.length≤xs.length from le_refl _),Nat.sub_self,List.getElem_cons_zero] at hit
  have addr:s.ptrs 43-1=base+xs.length:=by have v:=h.cursor;simp at v;omega
  have rem:s.ptrs 42-1=xs.length:=by have v:=h.remain;simp at v;omega
  have flag:u.ptrs 46=(if b then 1 else 0):=by simp [u,fetchOps,perform,Op.eval,addr,hit]
  have p1:u.ptrs 41=1:=h.one
  have val:u.ptrs 44=(rank ys:ℤ):=h.value
  have pow:u.ptrs 45=(2^ys.length:ℕ):=h.power
  let v:=if b then yesOp.eval d u else if rank ys=0 then u else noOp.eval d u
  have choose:∃z,Executes d branch u v z ∧ z≤4:=by
    cases b
    · have off:¬(Cond.pointerLE 41 46).test u:=by change ¬u.ptrs 41 ≤ u.ptrs 46;rw [p1,flag];decide
      by_cases k:rank ys=0
      · have z:¬(Cond.pointerLE 41 44).test u:=by change ¬u.ptrs 41 ≤ u.ptrs 44;rw [p1,val,k];decide
        exact ⟨_,by simpa [v,k,branch,right] using (Executes.ite_false off (Executes.ite_false (yes:=.atom noOp) z (Executes.skip u)) (yes:=.atom yesOp)),by decide⟩
      · have z:(Cond.pointerLE 41 44).test u:=by change u.ptrs 41 ≤ u.ptrs 44;rw [p1,val];omega
        exact ⟨_,by simpa [v,k,branch,right] using (Executes.ite_false off (Executes.ite_true (no:=.skip) z (Executes.atom noOp u)) (yes:=.atom yesOp)),by decide⟩
    · have on':(Cond.pointerLE 41 46).test u:=by change u.ptrs 41 ≤ u.ptrs 46;rw [p1,flag];decide
      exact ⟨_,by simpa [v,branch] using (Executes.ite_true (no:=right) on' (Executes.atom yesOp u)),by decide⟩
  obtain ⟨z,ex,tm⟩:=choose
  let t:=twice.eval d v
  refine ⟨t,_,.seq (line_exec d s fetchOps) (.seq ex (.atom _ _)),by change 3+(z+1)≤9;omega,?_⟩
  have old (j:ℕ) (hj:j≠44) : v.ptrs j=u.ptrs j:=by
    cases b <;> by_cases k:rank ys=0 <;> simp [v,k,yesOp,noOp,Op.eval,Function.update_of_ne hj]
  have mem:v.imem=s.imem:=by cases b <;> simp [v,yesOp,noOp,Op.eval,u,fetchOps,perform] <;> split <;> rfl
  refine ⟨(old 41 (by decide)).trans p1,(old 42 (by decide)).trans rem,(old 43 (by decide)).trans addr,?_,?_,?_⟩
  · cases b <;> by_cases k:rank ys=0 <;> simp [t,v,twice,yesOp,noOp,Op.eval,k,rank,prepend,val,pow]
  · change v.ptrs 45+v.ptrs 45=_
    rw [old 45 (by decide),pow,List.length_cons,pow_succ];push_cast;ring
  · intro j hj;change v.imem _=_;rw [mem]
    have q:=h.present j (by simp;omega)
    rw [List.getElem_append_left hj] at q
    exact q

theorem loop_run {n:ℕ} (d:Fin n→Fin n→ℝ) (base:ℤ) (xs ys:List Bool) (s:Store) (h:At base xs ys s) :
    ∃t z,Executes d loop s t z ∧ z≤2+11*xs.length ∧ t.ptrs 44=(rank (xs++ys):ℤ):=by
  induction xs using List.reverseRecOn generalizing ys s with
  | nil=>
    have off:¬(Cond.pointerLE 41 42).test s:=by change ¬s.ptrs 41 ≤ s.ptrs 42;rw [h.one,h.remain];decide
    exact ⟨s,_,.while_false off,by decide,h.value⟩
  | append_singleton xs b ih=>
    have on':(Cond.pointerLE 41 42).test s:=by change s.ptrs 41 ≤ s.ptrs 42;rw [h.one,h.remain];simp
    obtain ⟨v,z,one,len,hv⟩:=tick d base xs ys b s h
    obtain ⟨t,y,run,time,val⟩:=ih (b::ys) v hv
    refine ⟨t,_,.while_true on' one run,?_,by simpa [List.append_assoc] using val⟩
    simp only [List.length_append,List.length_singleton,Nat.mul_add,Nat.mul_one];omega

theorem kernel (n:ℕ) (d:Fin n→Fin n→ℝ) (s:Store) (bs:List Bool) (sz:s.ptrs 0=(bs.length:ℤ))
    (mem:∀j (hj:j<bs.length),s.imem (s.ptrs 30+(j:ℤ))=(if bs[j] then 1 else 0)) :
    ∃t z,Executes d program s t z ∧ z≤7+11*bs.length ∧ t.ptrs 44=(rank bs:ℤ):=by
  let u:=perform d s beginOps
  have atStart:At (s.ptrs 30) bs [] u:=by
    constructor <;> simp [u,beginOps,perform,Op.eval,sz,rank] <;> exact mem
  obtain ⟨t,z,run,time,ans⟩:=loop_run d (s.ptrs 30) bs [] u atStart
  exact ⟨t,_,.seq (line_exec d s _) run,by change 5+z≤_;omega,by simpa using ans⟩
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.LexMask

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.LexMask
open Compiler
set_option autoImplicit false
theorem indices_filter (bs:List Bool) :
   indices bs=(List.range bs.length).filter (fun i=>(bs[i]?).getD false):=by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>
    rw [List.length_cons,List.range_succ_eq_map]
    cases b <;> simp [indices,List.filter_map,Function.comp_def,ih]

theorem all_fields :
  ∃(cmd:Cmd) (key:List Bool→ℕ),IntegerCmd cmd ∧
    (∀bs:List Bool,key bs<2^bs.length) ∧
    (∀(a b:List Bool),a.length=b.length →
      let points:=fun xs:List Bool=>(List.range xs.length).filter (fun i=>(xs[i]?).getD false)
      key a<key b ↔ points a < points b) ∧
    ∀(n:ℕ) (d:Fin n→Fin n→ℝ) (s:Store) (bs:List Bool),s.ptrs 0=(bs.length:ℤ) →
      (∀j (hj:j<bs.length),s.imem (s.ptrs 30+(j:ℤ))=(if bs[j] then 1 else 0)) →
      ∃t z,Executes d cmd s t z ∧ z≤7+11*bs.length ∧ t.ptrs 44=(key bs:ℤ) ∧ t.imem=s.imem ∧ t.queries=s.queries ∧ (∀j<6,t.ptrs j=s.ptrs j):=by
  refine ⟨program,rank,?_,rank_bound,?_,?_⟩
  · simp [program,beginOps,loop,advance,fetchOps,branch,right,yesOp,noOp,twice,Relative.Machine.line,IntegerCmd,integerCond,integerOp]
  · intro a b len;simpa only [indices_filter] using rank_lt len
  · intro n d s bs sz m
    obtain ⟨t,z,ex,tm,out⟩:=kernel n d s bs sz m
    refine ⟨t,z,ex,tm,out,Machine.preserves ex .imem (by decide),Machine.preserves ex .queries (by decide),?_⟩
    intro j hj
    apply Machine.preserves ex (.ptr j)
    interval_cases j <;> decide
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.LexMask


open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution :
  ∃(cmd:Cmd) (key:List Bool→ℕ),IntegerCmd cmd ∧
    (∀bs:List Bool,key bs<2^bs.length) ∧
    (∀(a b:List Bool),a.length=b.length →
      let points:=fun xs:List Bool=>(List.range xs.length).filter (fun i=>(xs[i]?).getD false)
      key a<key b ↔ points a < points b) ∧
    ∀(n:ℕ) (d:Fin n→Fin n→ℝ) (s:Store) (bs:List Bool),s.ptrs 0=(bs.length:ℤ) →
      (∀j (hj:j<bs.length),s.imem (s.ptrs 30+(j:ℤ))=(if bs[j] then 1 else 0)) →
      ∃t z,Executes d cmd s t z ∧ z≤7+11*bs.length ∧ t.ptrs 44=(key bs:ℤ) ∧ t.imem=s.imem ∧ t.queries=s.queries ∧ (∀j<6,t.ptrs j=s.ptrs j) := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.LexMask.all_fields
