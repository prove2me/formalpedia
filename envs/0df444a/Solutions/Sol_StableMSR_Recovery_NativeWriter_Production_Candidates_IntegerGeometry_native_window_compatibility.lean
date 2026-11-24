-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.native_window_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T00:37:59.445943+00:00
-- url     : https://prove2.me/submissions/0d95dbe3-9120-4651-9991-f2ab59bd5572

import Definitions.Def_StableMSR_IntegerRegionalGeometry
set_option linter.all false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
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

def setPtr (s:Store) (j:ℕ) (z:ℤ) : Store := {s with ptrs:=Function.update s.ptrs j z}
def setReal (s:Store) (j:ℕ) (v:ℝ) : Store := {s with regs:=Function.update s.regs j v}
def one : ℕ:=7
def forCode (bound idx rem:ℕ) (body:Cmd) := Cmd.seq (line [.pointerConst idx 0,.pointerCopy rem bound])
  (.whileDo (.pointerLE one rem) (.seq body (line [.pointerInc idx,.pointerDec rem])))

theorem while_bounded {n:ℕ} (d:Fin n→Fin n→ℝ) (cond:Cond) (body:Cmd) (L C:ℕ) (I:ℕ→Store→Prop)
    (guard:∀i≤L,∀s,I i s→(cond.test s ↔ i<L))
    (step:∀i<L,∀s,I i s→∃t z,Executes d body s t z ∧ z≤C ∧ I (i+1) t)
    (s:Store) (init:I 0 s) :
    ∃t z,Executes d (.whileDo cond body) s t z ∧ z≤2+L*(2+C) ∧ I L t := by
  have go (k i:ℕ) (endAt:i+k=L) (u:Store) (iu:I i u) :
      ∃t z,Executes d (.whileDo cond body) u t z ∧ z≤2+k*(2+C) ∧ I L t:=by
    induction k generalizing i u with
    | zero=>
      have eq:i=L:=by omega
      refine ⟨u,2,.while_false (fun bad=>by have:= (guard i (by omega) u iu).mp bad;omega),by simp,eq ▸ iu⟩
    | succ k ih=>
      obtain ⟨v,z,ex,b,iv⟩:=step i (by omega) u iu
      obtain ⟨t,y,ey,e,it⟩:=ih (i+1) (by omega) v iv
      exact ⟨t,_,.while_true ((guard i (by omega) u iu).mpr (by omega)) ex ey,by rw [Nat.succ_mul];omega,it⟩
  exact go L 0 (by simp) s init

theorem for_run {n:ℕ} (d:Fin n→Fin n→ℝ) (b idx rem L C:ℕ) (body:Cmd) (s:Store) (I:ℕ→Store→Prop)
    (sep:idx≠rem ∧ idx≠b ∧ idx≠one ∧ rem≠one)
    (sf:safe (.ptr idx) body=true ∧ safe (.ptr rem) body=true ∧ safe (.ptr one) body=true)
    (stable:∀i u j z,j=idx ∨ j=rem → I i u→I i (setPtr u j z))
    (bound:s.ptrs b=(L:ℤ)) (start:s.ptrs one=1) (init:I 0 s)
    (step:∀i<L,∀u,I i u→u.ptrs idx=(i:ℤ)→∃t z,Executes d body u t z ∧ z≤C ∧ I (i+1) t) :
    ∃t z,Executes d (forCode b idx rem body) s t z ∧ z≤4+L*(C+4) ∧ I L t := by
  obtain ⟨ir,ib,io,ro⟩:=sep
  let initOps:List Op:=[.pointerConst idx 0,.pointerCopy rem b]
  let incOps:List Op:=[.pointerInc idx,.pointerDec rem]
  let u:=perform d s initOps
  let J:=fun i (q:Store)=>I i q ∧ q.ptrs idx=(i:ℤ) ∧ q.ptrs rem=(L:ℤ)-(i:ℤ) ∧ q.ptrs one=1
  have initial:u=setPtr (setPtr s idx 0) rem (L:ℤ):=by
    simp [u,initOps,perform,Op.eval,setPtr,Function.update_of_ne (Ne.symm ib),bound]
  have ju:J 0 u:=by
    rw [initial];refine ⟨stable 0 _ rem _ (Or.inr rfl) (stable 0 _ idx _ (Or.inl rfl) init),?_,?_,?_⟩ <;>
      simp [setPtr,Function.update_apply,ir,Ne.symm io,Ne.symm ro,start]
  have guard (i:ℕ) (hi:i≤L) (q:Store) (h:J i q) : (Cond.pointerLE one rem).test q ↔ i<L:=by
    change q.ptrs one ≤ q.ptrs rem ↔ _;rw [h.2.2.2,h.2.2.1];omega
  have tick (i:ℕ) (hi:i<L) (q:Store) (h:J i q) :
      ∃t z,Executes d (.seq body (line incOps)) q t z ∧ z≤C+2 ∧ J (i+1) t:=by
    obtain ⟨v,z,ex,zc,vp⟩:=step i hi q h.1 h.2.1
    have vi:v.ptrs idx=(i:ℤ):=(preserves ex _ sf.1).trans h.2.1
    have vr:v.ptrs rem=(L:ℤ)-(i:ℤ):=(preserves ex _ sf.2.1).trans h.2.2.1
    have vo:v.ptrs one=1:=(preserves ex _ sf.2.2).trans h.2.2.2
    let t:=perform d v incOps
    have eq:t=setPtr (setPtr v idx ((i:ℤ)+1)) rem ((L:ℤ)-(i:ℤ)-1):=by
      simp [t,incOps,perform,Op.eval,setPtr,Function.update_of_ne (Ne.symm ir),vi,vr]
    refine ⟨t,_,.seq ex (line_exec d v incOps),by change z+2≤C+2;omega,?_⟩
    rw [eq];refine ⟨stable _ _ rem _ (Or.inr rfl) (stable _ _ idx _ (Or.inl rfl) vp),?_,?_,?_⟩ <;>
      simp [setPtr,Function.update_apply,ir,Ne.symm io,Ne.symm ro,vo] <;> omega
  obtain ⟨t,z,ex,cost,ok⟩:=while_bounded d _ _ L (C+2) J guard tick u ju
  refine ⟨t,_,.seq (line_exec d s initOps) ex,?_,ok.1⟩
  change 2+z≤_;have eq:2+(C+2)=C+4:=by omega
  rw [eq] at cost;omega

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap
open Compiler OracleQueries Relative.Machine
set_option autoImplicit false
set_option maxHeartbeats 1800000

inductive Pred where | reg (r:ℕ) | both (a b:Pred) | neg (a:Pred)
def Pred.either (a b:Pred):Pred:=.neg (.both (.neg a) (.neg b))
def Pred.eval : Pred→Store→Bool
  | .reg r,s=>decide (s.ptrs one ≤ s.ptrs r)
  | .both a b,s=>a.eval s && b.eval s | .neg a,s=> !a.eval s
def Pred.cost : Pred→ℕ | .reg _=>2 | .both a b=>a.cost+b.cost | .neg a=>a.cost
def Pred.branch : Pred→Cmd→Cmd→Cmd
  | .reg r,y,n=>.ite (.pointerLE one r) y n
  | .both a b,y,n=>a.branch (b.branch y n) n
  | .neg a,y,n=>a.branch n y

theorem Pred.branch_run {n:ℕ} (d:Fin n→Fin n→ℝ) (p:Pred) (y no:Cmd) (s t:Store) (z:ℕ)
    (ex:Executes d (if p.eval s then y else no) s t z) :
    ∃k,Executes d (p.branch y no) s t k ∧ k≤z+p.cost:=by
  induction p generalizing y no z with
  | reg r=>
    by_cases h:s.ptrs one ≤ s.ptrs r
    · simp only [Pred.eval,decide_eq_true h,if_true] at ex
      exact ⟨_,.ite_true h ex,by simp only [Pred.cost];omega⟩
    · simp only [Pred.eval,decide_eq_false h,Bool.false_eq_true,if_false] at ex
      exact ⟨_,.ite_false h ex,by simp only [Pred.cost];omega⟩
  | neg a ih=>
    apply ih
    cases e:a.eval s <;> simpa [Pred.eval,e] using ex
  | both a b ih jh=>
    cases e:a.eval s with
    | false=>
      have out:Executes d no s t z:=by simpa [Pred.eval,e] using ex
      obtain ⟨k,run,tm⟩:=ih (b.branch y no) no z (by simpa [e] using out)
      exact ⟨k,run,by simp only [Pred.cost];omega⟩
    | true=>
      have out:Executes d (if b.eval s then y else no) s t z:=by simpa [Pred.eval,e] using ex
      obtain ⟨j,rj,tj⟩:=jh y no z out
      obtain ⟨k,run,tm⟩:=ih (b.branch y no) no j (by simpa [e] using rj)
      exact ⟨k,run,by simp only [Pred.cost];omega⟩

structure Update where
  dst:ℕ
  value:ℤ
  test:Pred
def Update.code (u:Update) := u.test.branch (.atom (.pointerConst u.dst u.value)) (.atom (.pointerCopy u.dst u.dst))
def Update.next (u:Update) (s:Store) := setPtr s u.dst (if u.test.eval s then u.value else s.ptrs u.dst)
theorem Update.run {n:ℕ} (d:Fin n→Fin n→ℝ) (op:Update) (s:Store) :
    ∃k,Executes d op.code s (op.next s) k ∧ k≤1+op.test.cost:=by
  apply Pred.branch_run d op.test _ _ _ _ 1
  cases e:op.test.eval s <;> simp only [e,Update.next,Bool.false_eq_true,if_false,if_true]
  · exact .atom _ _
  · exact .atom _ _

def updates : List Update→Cmd | []=>.skip | u::us=>.seq u.code (updates us)
def applied : List Update→Store→Store | [],s=>s | u::us,s=>applied us (u.next s)
def updateCost : List Update→ℕ | []=>0 | u::us=>1+u.test.cost+updateCost us
theorem applied_run {n:ℕ} (d:Fin n→Fin n→ℝ) (xs:List Update) (s:Store) :
    ∃z,Executes d (updates xs) s (applied xs s) z ∧ z≤updateCost xs:=by
  induction xs generalizing s with
  | nil=>exact ⟨0,.skip _,by rfl⟩
  | cons u us ih=>
    obtain ⟨i,ex,tm⟩:=u.run d s
    obtain ⟨j,ey,b⟩:=ih (u.next s)
    exact ⟨_,.seq ex ey,by change i+j≤1+u.test.cost+updateCost us;omega⟩

def bit (b:Bool):ℤ:=if b then 1 else 0
theorem read_bit (b:Bool) : decide ((1:ℤ)≤bit b)=b:=by cases b <;> decide
theorem raise_bit (a b:Bool) : (if b then (1:ℤ) else bit a)=bit (a || b):=by cases a <;> cases b <;> rfl

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap
open Compiler OracleQueries Relative.Machine
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxRecDepth 18000

structure Columns where
  left:ℕ→Bool
  right:ℕ→Bool
  ownL:ℕ→Bool
  ownR:ℕ→Bool
structure Bases where
  left:ℤ
  right:ℤ
  ownL:ℤ
  ownR:ℤ
def Reads (n:ℕ) (F:Columns) (B:Bases) (s:Store) := ∀i<n,
  s.imem (B.left+(i:ℤ))=bit (F.left i) ∧ s.imem (B.right+(i:ℤ))=bit (F.right i) ∧
  s.imem (B.ownL+(i:ℤ))=bit (F.ownL i) ∧ s.imem (B.ownR+(i:ℤ))=bit (F.ownR i)
def differs (x y:Bool) := !( (!(x && !y)) && (!((!x) && y)) )
def seen (i:ℕ) (f:ℕ→Bool) := (List.range i).any f
theorem seen_next (i:ℕ) (f:ℕ→Bool) : seen (i+1) f=(seen i f || f i):=by simp [seen,List.range_succ]
def testL (F:Columns) (p:ℕ):=F.left p && F.ownL p
def testR (F:Columns) (p:ℕ):=F.right p && F.ownR p
def testI (F:Columns) (p:ℕ):=F.left p && F.right p
def testD (F:Columns) (p:ℕ):=differs (F.left p) (F.right p)
def bad (n:ℕ) (F:Columns) := seen n (testL F) && seen n (testR F) && seen n (testI F) && seen n (testD F)

def flags : List Update:=[
  ⟨44,1,.both (.reg 54) (.reg 56)⟩,⟨45,1,.both (.reg 55) (.reg 57)⟩,
  ⟨46,1,.both (.reg 54) (.reg 55)⟩,
  ⟨47,1,Pred.either (.both (.reg 54) (.neg (.reg 55))) (.both (.neg (.reg 54)) (.reg 55))⟩]
def readOps:List Op:=[.integerLoad 54 40,.integerLoad 55 41,.integerLoad 56 42,.integerLoad 57 43]
def bumpOps:List Op:=[.pointerInc 40,.pointerInc 41,.pointerInc 42,.pointerInc 43]
def pairStep:=Cmd.seq (line readOps) (.seq (updates flags) (line bumpOps))
def pairLoop:=forCode 0 48 49 pairStep
def baseOps:List Op:=[.pointerCopy 40 35,.pointerCopy 41 36,.pointerCopy 42 32,.pointerCopy 43 33,
  .pointerConst 44 0,.pointerConst 45 0,.pointerConst 46 0,.pointerConst 47 0]
def reject:Update:=⟨37,0,.both (.both (.both (.reg 44) (.reg 45)) (.reg 46)) (.reg 47)⟩
def pairCode:=Cmd.seq (line baseOps) (.seq pairLoop reject.code)

structure Scan (n:ℕ) (F:Columns) (B:Bases) (i:ℕ) (s:Store) : Prop where
  oneOK:s.ptrs one=1
  read:Reads n F B s
  left:s.ptrs 40=B.left+(i:ℤ)
  right:s.ptrs 41=B.right+(i:ℤ)
  ownerL:s.ptrs 42=B.ownL+(i:ℤ)
  ownerR:s.ptrs 43=B.ownR+(i:ℤ)
  l:s.ptrs 44=bit (seen i (testL F))
  r:s.ptrs 45=bit (seen i (testR F))
  inter:s.ptrs 46=bit (seen i (testI F))
  diff:s.ptrs 47=bit (seen i (testD F))

theorem scan_one {k:ℕ} (d:Fin k→Fin k→ℝ) (n:ℕ) (F:Columns) (B:Bases) (i:ℕ) (hi:i<n) (s:Store) (h:Scan n F B i s) :
    ∃t z,Executes d pairStep s t z ∧ z≤32 ∧ Scan n F B (i+1) t:=by
  let u:=perform d s readOps
  let v:=applied flags u
  let t:=perform d v bumpOps
  obtain ⟨z,ex,bz⟩:=applied_run d flags u
  have exv:Executes d (updates flags) u v z:=ex
  have exec:Executes d pairStep s t (4+(z+4)):=.seq (line_exec d s readOps) (.seq exv (line_exec d v bumpOps))
  have cost:z≤24:=bz
  have rd:=h.read i hi
  have rr:u.ptrs 54=bit (F.left i) ∧ u.ptrs 55=bit (F.right i) ∧
      u.ptrs 56=bit (F.ownL i) ∧ u.ptrs 57=bit (F.ownR i):=by
    simp [u,readOps,perform,Op.eval,h.left,h.right,h.ownerL,h.ownerR,rd.1,rd.2.1,rd.2.2.1,rd.2.2.2]
  have u7:u.ptrs one=1:=h.oneOK
  have mm:t.imem=s.imem:=preserves exec .imem (by decide)
  have advance (j:ℕ) (hj:j=40 ∨ j=41 ∨ j=42 ∨ j=43) : t.ptrs j=s.ptrs j+1:=by
    rcases hj with rfl|rfl|rfl|rfl <;> rfl
  refine ⟨t,_,exec,by omega,(preserves exec (.ptr one) (by decide)).trans h.oneOK,
    fun j hj=>by simpa only [mm] using h.read j hj,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [advance _ (by decide),h.left];push_cast;ring
  · rw [advance _ (by decide),h.right];push_cast;ring
  · rw [advance _ (by decide),h.ownerL];push_cast;ring
  · rw [advance _ (by decide),h.ownerR];push_cast;ring
  all_goals have l:u.ptrs 44=bit (seen i (testL F)):=h.l
  all_goals have r:u.ptrs 45=bit (seen i (testR F)):=h.r
  all_goals have inter:u.ptrs 46=bit (seen i (testI F)):=h.inter
  all_goals have diff:u.ptrs 47=bit (seen i (testD F)):=h.diff
  all_goals simp [t,v,bumpOps,perform,Op.eval,flags,applied,Update.next,Pred.either,Pred.eval,setPtr,one,
    show u.ptrs 7=1 from u7,rr.1,rr.2.1,rr.2.2.1,rr.2.2.2,l,r,inter,diff,read_bit,seen_next,raise_bit,
    testL,testR,testI,testD,differs]
  all_goals cases el:F.left i <;> cases er:F.right i <;> cases ea:F.ownL i <;> cases eb:F.ownR i <;> simp [el,er,ea,eb,bit]

theorem pair_run {k:ℕ} (d:Fin k→Fin k→ℝ) (n:ℕ) (F:Columns) (B:Bases) (s:Store)
    (points:s.ptrs 0=(n:ℤ)) (start:s.ptrs one=1) (rd:Reads n F B s)
    (bases:s.ptrs 35=B.left ∧ s.ptrs 36=B.right ∧ s.ptrs 32=B.ownL ∧ s.ptrs 33=B.ownR) :
    ∃t z,Executes d pairCode s t z ∧ z≤21+36*n ∧ t.ptrs 37=(if bad n F then 0 else s.ptrs 37):=by
  let u:=perform d s baseOps
  have init:Scan n F B 0 u:=by
    refine ⟨start,rd,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      simp [u,baseOps,perform,Op.eval,bases.1,bases.2.1,bases.2.2.1,bases.2.2.2,seen,bit]
  obtain ⟨v,z,ex,tm,res⟩:=for_run d 0 48 49 n 32 pairStep u (fun i t=>Scan n F B i t)
    (by decide) (by decide) (by
      intro i t j q hj h;rcases hj with rfl|rfl <;> exact ⟨h.oneOK,h.read,h.left,h.right,h.ownerL,h.ownerR,h.l,h.r,h.inter,h.diff⟩)
    points start init (by intro i hi t h idx;exact scan_one d n F B i hi t h)
  obtain ⟨y,ey,byy⟩:=reject.run d v
  have ct:y≤9:=byy
  have keep:v.ptrs 37=s.ptrs 37:=(preserves ex (.ptr 37) (by decide)).trans rfl
  have cond:reject.test.eval v=bad n F:=by simp [reject,Pred.eval,res.oneOK,res.l,res.r,res.inter,res.diff,read_bit,bad]
  refine ⟨_,_,.seq (line_exec d s baseOps) (.seq ex ey),?_,?_⟩
  · change 8+(z+y)≤_;omega
  · simp [Update.next,setPtr,cond,keep,reject] at * <;> rfl

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap
open Compiler OracleQueries Relative.Machine
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 24000

structure Grid (n:ℕ) (L R:ℕ→ℕ→Bool) (A B:ℕ→Bool) (s:Store) : Prop where
  pts:s.ptrs 0=(n:ℤ)
  oneOK:s.ptrs one=1
  left:∀i<n,∀p<n,s.imem (s.ptrs 30+(i:ℤ)*(n:ℤ)+(p:ℤ))=bit (L i p)
  right:∀i<n,∀p<n,s.imem (s.ptrs 31+(i:ℤ)*(n:ℤ)+(p:ℤ))=bit (R i p)
  ownL:∀p<n,s.imem (s.ptrs 32+(p:ℤ))=bit (A p)
  ownR:∀p<n,s.imem (s.ptrs 33+(p:ℤ))=bit (B p)
def gridFields:List Field:=[.ptr 0,.ptr one,.ptr 30,.ptr 31,.ptr 32,.ptr 33,.imem]
theorem Grid.keep {n k:ℕ} {L R:ℕ→ℕ→Bool} {A B:ℕ→Bool} {s t:Store} {d:Fin k→Fin k→ℝ} {cmd:Cmd} {z:ℕ}
    (h:Grid n L R A B s) (ex:Executes d cmd s t z) (hc:gridFields.all (fun f=>safe f cmd)=true) : Grid n L R A B t:=by
  have pr (f:Field) (hf:f∈gridFields):=preserves ex f (List.all_eq_true.mp hc f hf)
  have mm:t.imem=s.imem:=pr .imem (by simp [gridFields])
  have keep (j:ℕ) (hj:j=30 ∨ j=31 ∨ j=32 ∨ j=33) : t.ptrs j=s.ptrs j:=by
    apply pr (.ptr j);rcases hj with rfl|rfl|rfl|rfl <;> simp [gridFields]
  refine ⟨(pr (.ptr 0) (by simp [gridFields])).trans h.pts,(pr (.ptr one) (by simp [gridFields])).trans h.oneOK,?_,?_,?_,?_⟩
  · intro i hi p hp;rw [mm,keep 30 (by decide)];exact h.left i hi p hp
  · intro i hi p hp;rw [mm,keep 31 (by decide)];exact h.right i hi p hp
  · intro p hp;rw [mm,keep 32 (by decide)];exact h.ownL p hp
  · intro p hp;rw [mm,keep 33 (by decide)];exact h.ownR p hp
theorem Grid.ptr {n:ℕ} {L R:ℕ→ℕ→Bool} {A B:ℕ→Bool} {s:Store} (h:Grid n L R A B s) (j:ℕ) (v:ℤ)
    (hj:j=50 ∨ j=51 ∨ j=52 ∨ j=53) : Grid n L R A B (setPtr s j v):=by
  rcases hj with rfl|rfl|rfl|rfl <;> exact ⟨h.pts,h.oneOK,h.left,h.right,h.ownL,h.ownR⟩

def okAll (j:ℕ) (f:ℕ→Bool) := (List.range j).all f
theorem okAll_next (j:ℕ) (f:ℕ→Bool) : okAll (j+1) f=(okAll j f && f j):=by simp [okAll,List.range_succ]
theorem lower_bit (x e:Bool) : (if e then (0:ℤ) else bit x)=bit (x && !e):=by cases x <;> cases e <;> rfl
def col (L R:ℕ→ℕ→Bool) (A B:ℕ→Bool) (i j:ℕ) : Columns:=⟨L i,R j,A,B⟩
def innerStep:=Cmd.seq pairCode (.atom (.pointerAdd 36 36 0))
def inner:=forCode 0 50 51 innerStep
def stepRow:=Cmd.seq (.atom (.pointerCopy 36 31)) (.seq inner (.atom (.pointerAdd 35 35 0)))
def outer:=forCode 0 52 53 stepRow
def gridInit:List Op:=[.pointerConst 7 1,.pointerCopy 35 30,.pointerConst 37 1]
def allCode:=Cmd.seq (line gridInit) outer

theorem right_run {n k:ℕ} (d:Fin k→Fin k→ℝ) (L R:ℕ→ℕ→Bool) (A B:ℕ→Bool) (i:ℕ) (hi:i<n)
    (s:Store) (g:Grid n L R A B s) (q:Bool) (acc:s.ptrs 37=bit q)
    (left:s.ptrs 35=s.ptrs 30+(i:ℤ)*(n:ℤ)) (right:s.ptrs 36=s.ptrs 31) :
    ∃t z,Executes d inner s t z ∧ z≤4+n*(26+36*n) ∧ t.ptrs 37=bit (q && okAll n (fun j=> !bad n (col L R A B i j))) := by
  let good:=fun j=> !bad n (col L R A B i j)
  let I:=fun (j:ℕ) (v:Store)=>Grid n L R A B v ∧ v.ptrs 35=v.ptrs 30+(i:ℤ)*(n:ℤ) ∧
    v.ptrs 36=v.ptrs 31+(j:ℤ)*(n:ℤ) ∧ v.ptrs 37=bit (q && okAll j good)
  have st:I 0 s:=⟨g,left,by simpa using right,by simpa [okAll] using acc⟩
  obtain ⟨t,z,ex,tm,res⟩:=for_run d 0 50 51 n (22+36*n) innerStep s I (by decide) (by decide)
    (by intro j u a b hj hu;refine ⟨hu.1.ptr a b (by rcases hj with rfl|rfl <;> decide),?_⟩
        rcases hj with rfl|rfl <;> exact hu.2) g.pts g.oneOK st (by
      intro j hj u hu ix
      let base:Bases:=⟨u.ptrs 35,u.ptrs 36,u.ptrs 32,u.ptrs 33⟩
      let F:=col L R A B i j
      have rd:Reads n F base u:=by
        intro p hp
        exact ⟨by simpa only [base,hu.2.1,F,col] using hu.1.left i hi p hp,
          by simpa only [base,hu.2.2.1,F,col] using hu.1.right j hj p hp,hu.1.ownL p hp,hu.1.ownR p hp⟩
      obtain ⟨v,y,ex,tm,res⟩:=pair_run d n F base u hu.1.pts hu.1.oneOK rd ⟨rfl,rfl,rfl,rfl⟩
      let t:=(Op.pointerAdd 36 36 0).eval d v
      have et:Executes d innerStep u t (y+1):=.seq ex (.atom _ _)
      have fin:t.ptrs 37=bit ((q && okAll j good) && !bad n F):=by
        change v.ptrs 37=_;rw [res,hu.2.2.2,lower_bit]
      have v36:v.ptrs 36=u.ptrs 36:=preserves ex (.ptr 36) (by decide)
      have gp:=hu.1.keep ex (by decide)
      refine ⟨t,_,et,by omega,hu.1.keep et (by decide),?_,?_,?_⟩
      · rw [show t.ptrs 35=u.ptrs 35 from preserves et (.ptr 35) (by decide),
            show t.ptrs 30=u.ptrs 30 from preserves et (.ptr 30) (by decide)];exact hu.2.1
      · change v.ptrs 36+v.ptrs 0=v.ptrs 31+_
        rw [v36,hu.2.2.1,gp.pts,show v.ptrs 31=u.ptrs 31 from preserves ex (.ptr 31) (by decide)]
        push_cast;ring
      · simpa only [okAll_next,←Bool.and_assoc,good,F] using fin)
  refine ⟨t,z,ex,?_,res.2.2.2⟩
  simpa only [show 22+36*n+4=26+36*n by omega] using tm

theorem all_run {n k:ℕ} (d:Fin k→Fin k→ℝ) (L R:ℕ→ℕ→Bool) (A B:ℕ→Bool) (s:Store)
    (pts:s.ptrs 0=(n:ℤ)) (ll:∀i<n,∀p<n,s.imem (s.ptrs 30+(i:ℤ)*(n:ℤ)+(p:ℤ))=bit (L i p))
    (rr:∀i<n,∀p<n,s.imem (s.ptrs 31+(i:ℤ)*(n:ℤ)+(p:ℤ))=bit (R i p))
    (aa:∀p<n,s.imem (s.ptrs 32+(p:ℤ))=bit (A p)) (bb:∀p<n,s.imem (s.ptrs 33+(p:ℤ))=bit (B p)) :
    ∃t z,Executes d allCode s t z ∧ z≤100*(1+n)^3 ∧
      t.ptrs 37=bit (okAll n (fun i=>okAll n (fun j=> !bad n (col L R A B i j)))):=by
  let u:=perform d s gridInit
  let good:=fun i=>okAll n (fun j=> !bad n (col L R A B i j))
  let I:=fun (i:ℕ) (v:Store)=>Grid n L R A B v ∧ v.ptrs 35=v.ptrs 30+(i:ℤ)*(n:ℤ) ∧ v.ptrs 37=bit (okAll i good)
  have ig:Grid n L R A B u:=⟨pts,rfl,ll,rr,aa,bb⟩
  have init:I 0 u:=⟨ig,by simp [u,gridInit,perform,Op.eval],by simp [u,gridInit,perform,Op.eval,bit,okAll]⟩
  obtain ⟨t,z,ex,tm,res⟩:=for_run d 0 52 53 n (6+n*(26+36*n)) stepRow u I (by decide) (by decide)
    (by intro i t j z hj ht;refine ⟨ht.1.ptr j z (by rcases hj with rfl|rfl <;> decide),?_⟩
        rcases hj with rfl|rfl <;> exact ht.2) pts ig.oneOK init (by
      intro i hi v hv idx
      let w:=(Op.pointerCopy 36 31).eval d v
      have ew:Executes d (.atom (.pointerCopy 36 31)) v w 1:=.atom _ _
      obtain ⟨q,y,ex,tm,hq⟩:=right_run d L R A B i hi w (hv.1.keep ew (by decide)) (okAll i good) hv.2.2 hv.2.1 (by rfl)
      let t:=(Op.pointerAdd 35 35 0).eval d q
      have et:Executes d stepRow v t (1+(y+1)):=.seq ew (.seq ex (.atom _ _))
      have p35:q.ptrs 35=v.ptrs 35:=(preserves ex (.ptr 35) (by decide)).trans rfl
      have p30:q.ptrs 30=v.ptrs 30:=(preserves ex (.ptr 30) (by decide)).trans rfl
      have g:Grid n L R A B q:=(hv.1.keep ew (by decide)).keep ex (by decide)
      refine ⟨t,_,et,by omega,hv.1.keep et (by decide),?_,?_⟩
      · change q.ptrs 35+q.ptrs 0=q.ptrs 30+_;rw [p35,p30,hv.2.1,g.pts];push_cast;ring
      · change q.ptrs 37=_;rw [okAll_next];exact hq)
  exact ⟨t,_,.seq (line_exec d s gridInit) ex,by change 3+z≤_;nlinarith,res.2.2⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap
open Compiler OracleQueries WindowCSP Relative.Machine
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 24000

def rowAt {n:ℕ} (P:Fin n→Cluster n) (i p:ℕ) :=
  if hi:i<n then if hp:p<n then decide ((⟨p,hp⟩:Fin n)∈P ⟨i,hi⟩) else false else false
def ownAt {n:ℕ} (own:Fin n→Fin n) (a:Fin n) (p:ℕ) :=
  if hp:p<n then decide (own ⟨p,hp⟩=a) else false
theorem row_val {n:ℕ} (P:Fin n→Cluster n) (i p:Fin n) : rowAt P i.val p.val=decide (p∈P i):=by simp [rowAt,p.isLt,i.isLt]
theorem own_val {n:ℕ} (own:Fin n→Fin n) (a p:Fin n) : ownAt own a p.val=decide (own p=a):=by simp [ownAt,p.isLt]
theorem seen_fin (n:ℕ) (f:ℕ→Bool) : seen n f=true ↔ ∃p:Fin n,f p.val=true:=by
  simp only [seen,List.any_eq_true,List.mem_range]
  exact ⟨fun ⟨p,h,v⟩=>⟨⟨p,h⟩,v⟩,fun ⟨p,v⟩=>⟨p.val,p.isLt,v⟩⟩
theorem all_fin (n:ℕ) (f:ℕ→Bool) : okAll n f=true ↔ ∀p:Fin n,f p.val=true:=by
  simp only [okAll,List.all_eq_true,List.mem_range]
  exact ⟨fun h p=>h p.val p.isLt,fun h p hp=>h ⟨p,hp⟩⟩
theorem differs_iff (x y:Bool):differs x y=true ↔ x≠y:=by cases x <;> cases y <;> decide
theorem mismatch {n:ℕ} (C D:Cluster n) : (∃p:Fin n,decide (p∈C) ≠ decide (p∈D)) ↔ C≠D:=by
  constructor
  · rintro ⟨p,ne⟩ rfl;exact ne rfl
  · intro ne;by_contra absent;apply ne
    ext p;have eq:decide (p∈C)=decide (p∈D):=by by_contra h;exact absent ⟨p,h⟩
    simpa only [decide_eq_decide] using eq

theorem bad_iff {n:ℕ} (L R:Fin n→Cluster n) (own:Fin n→Fin n) (a b i j:Fin n) :
    bad n (col (rowAt L) (rowAt R) (ownAt own a) (ownAt own b) i.val j.val)=true ↔
      touches own a (L i) ∧ touches own b (R j) ∧ ((L i)∩(R j)).Nonempty ∧ L i≠R j:=by
  simp only [bad,Bool.and_eq_true,seen_fin,testL,testR,testI,testD,col,row_val,own_val,decide_eq_true_eq,differs_iff,mismatch]
  simp only [touches,Finset.Nonempty,Finset.mem_inter];tauto

theorem compatible_iff {n:ℕ} (L R:Fin n→Cluster n) (own:Fin n→Fin n) (a b:Fin n) :
    okAll n (fun i=>okAll n (fun j=> !bad n (col (rowAt L) (rowAt R) (ownAt own a) (ownAt own b) i j)))=true ↔
      compatible own a b (Finset.univ.image L) (Finset.univ.image R):=by
  simp only [all_fin,Bool.not_eq_true',Bool.eq_false_iff]
  constructor
  · intro chk C hc D hd inter
    obtain ⟨memC,tC⟩:=Finset.mem_filter.mp hc
    obtain ⟨memD,tD⟩:=Finset.mem_filter.mp hd
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp memC;obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp memD
    by_contra ne;exact chk i j ((bad_iff L R own a b i j).mpr ⟨tC,tD,inter,ne⟩)
  · intro comp i j problem
    obtain ⟨tC,tD,meet,ne⟩:=(bad_iff L R own a b i j).mp problem
    exact ne (comp _ (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ i),tC⟩) _
      (Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ j),tD⟩) meet)

theorem grid_correct (n:ℕ) (d:Fin n→Fin n→ℝ) (s:Store) (own:Fin n→Fin n) (a b:Fin n) (L R:Fin n→Cluster n)
    (pts:s.ptrs 0=(n:ℤ)) (rows:∀i p:Fin n,s.imem (s.ptrs 30+(i.val:ℤ)*(n:ℤ)+(p.val:ℤ))=(if p∈L i then 1 else 0) ∧
      s.imem (s.ptrs 31+(i.val:ℤ)*(n:ℤ)+(p.val:ℤ))=(if p∈R i then 1 else 0))
    (owners:∀p:Fin n,s.imem (s.ptrs 32+(p.val:ℤ))=(if own p=a then 1 else 0) ∧
      s.imem (s.ptrs 33+(p.val:ℤ))=(if own p=b then 1 else 0)) :
    ∃t z,Executes d allCode s t z ∧ z≤100*(1+n)^3 ∧ t.imem=s.imem ∧ t.mem=s.mem ∧ t.queries=s.queries ∧
      (∀j<6,t.ptrs j=s.ptrs j) ∧ t.ptrs 37=(if compatible own a b (Finset.univ.image L) (Finset.univ.image R) then 1 else 0):=by
  obtain ⟨t,z,ex,tm,out⟩:=all_run d (rowAt L) (rowAt R) (ownAt own a) (ownAt own b) s pts
    (by intro i hi p hp;simpa [rowAt,hi,hp,bit] using (rows ⟨i,hi⟩ ⟨p,hp⟩).1)
    (by intro i hi p hp;simpa [rowAt,hi,hp,bit] using (rows ⟨i,hi⟩ ⟨p,hp⟩).2)
    (by intro p hp;simpa [ownAt,hp,bit] using (owners ⟨p,hp⟩).1)
    (by intro p hp;simpa [ownAt,hp,bit] using (owners ⟨p,hp⟩).2)
  refine ⟨t,z,ex,tm,preserves ex .imem (by decide),preserves ex .mem (by decide),preserves ex .queries (by decide),?_,?_⟩
  · intro j hj;apply preserves ex (.ptr j);interval_cases j <;> decide
  · rw [out];simp only [bit,compatible_iff]

theorem integer_grid : IntegerCmd allCode:=by
  unfold allCode gridInit outer stepRow inner innerStep pairCode baseOps pairLoop pairStep readOps flags bumpOps reject
  simp [forCode,line,updates,Update.code,Pred.branch,Pred.either,IntegerCmd,integerOp,integerCond]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
theorem solution :
  ∃cmd:Cmd,IntegerCmd cmd ∧ ∀(n:ℕ) (d:Fin n→Fin n→ℝ) (s:Store) (own:Fin n→Fin n) (a b:Fin n)
    (L R:Fin n→Cluster n),s.ptrs 0=(n:ℤ) →
    (∀i p:Fin n,s.imem (s.ptrs 30+(i.val:ℤ)*(n:ℤ)+(p.val:ℤ))=(if p∈L i then 1 else 0) ∧
      s.imem (s.ptrs 31+(i.val:ℤ)*(n:ℤ)+(p.val:ℤ))=(if p∈R i then 1 else 0)) →
    (∀p:Fin n,s.imem (s.ptrs 32+(p.val:ℤ))=(if own p=a then 1 else 0) ∧
      s.imem (s.ptrs 33+(p.val:ℤ))=(if own p=b then 1 else 0)) →
    ∃t z,Executes d cmd s t z ∧ z≤100*(1+n)^3 ∧ t.imem=s.imem ∧ t.mem=s.mem ∧ t.queries=s.queries ∧
      (∀j<6,t.ptrs j=s.ptrs j) ∧ t.ptrs 37=(if compatible own a b (Finset.univ.image L) (Finset.univ.image R) then 1 else 0) := ⟨StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap.allCode,StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap.integer_grid,StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.Bitmap.grid_correct⟩
