-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.native_metric_table
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T00:20:45.986149+00:00
-- url     : https://prove2.me/submissions/ec70c96d-1fbd-41b1-aa65-c9ac38e95c92

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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open Compiler OracleQueries WindowCSP SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem samples_len (x:World) : (samples x).length=x.n*x.n:=by
  have calcLen (ls:List (Fin x.n)) :
      (ls.flatMap (fun a=>(List.finRange x.n).map (x.dist a))).length=ls.length*x.n:=by
    induction ls with
    | nil=>simp
    | cons a ls ih=>simp [ih,Nat.succ_mul,Nat.add_comm]
  simpa [samples] using calcLen (List.finRange x.n)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
open Compiler OracleQueries Relative.Machine
set_option autoImplicit false
set_option maxHeartbeats 1800000

def CacheAt (ds:List ℝ) (s:Store) := ∀j (hj:j<ds.length),s.mem (j:ℤ)=ds[j]
structure Cached (n q:ℕ) (ds:List ℝ) (s:Store) : Prop where
  points : s.ptrs 0=(n:ℤ)
  oneOK : s.ptrs one=1
  next : s.ptrs 8=(ds.length:ℤ)
  calls : s.queries=q+ds.length
  resident : CacheAt ds s

theorem Cached.ptr {n q j:ℕ} {ds:List ℝ} {s:Store} (h:Cached n q ds s) (z:ℤ)
    (a:j≠0) (b:j≠one) (c:j≠8) : Cached n q ds (setPtr s j z) := by
  refine ⟨?_,?_,?_,h.calls,h.resident⟩ <;> simp only [setPtr,Function.update_of_ne (Ne.symm a),
    Function.update_of_ne (Ne.symm b),Function.update_of_ne (Ne.symm c),h.points,h.oneOK,h.next]

def insertOps:List Op:=[.distance 0 9 11,.realStore 8 0,.pointerInc 8]
def cacheRow:=forCode 0 11 12 (line insertOps)
def loadCache:=forCode 0 9 10 cacheRow
def rowsOf (x:World) (ls:List (Fin x.n)) := ls.flatMap fun a=>(List.finRange x.n).map (x.dist a)

theorem insert_ok (x:World) (s:Store) (q:ℕ) (ds:List ℝ) (h:Cached x.n q ds s) (a b:Fin x.n)
    (ar:s.ptrs 9=(a.val:ℤ)) (br:s.ptrs 11=(b.val:ℤ)) :
    Cached x.n q (ds++[x.dist a b]) (perform x.dist s insertOps) := by
  have dist:MinSumFPT.oracleAnswer x.dist (s.ptrs 9) (s.ptrs 11)=x.dist a b:=by
    simp [ar,br,MinSumFPT.oracleAnswer,MinSumFPT.toPoint,a.isLt,b.isLt]
  let t:=perform x.dist s insertOps
  have mem:t.mem=Function.update s.mem (ds.length:ℤ) (x.dist a b):=by simp [t,insertOps,perform,Op.eval,dist,h.next]
  refine ⟨h.points,h.oneOK,?_,?_,?_⟩
  · simp [insertOps,perform,Op.eval,h.next]
  · simp [insertOps,perform,Op.eval,h.calls,Nat.add_assoc]
  · intro j hj;change t.mem (j:ℤ)=_;rw [mem]
    by_cases old:j<ds.length
    · rw [Function.update_of_ne (by exact_mod_cast Nat.ne_of_lt old),h.resident j old,List.getElem_append_left old]
    · have eq:j=ds.length:=by simp at hj;omega
      subst j;simp

theorem cache_one (x:World) (s:Store) (q:ℕ) (pre:List ℝ) (a:Fin x.n)
    (h:Cached x.n q pre s) (ar:s.ptrs 9=(a.val:ℤ)) :
    ∃t z,Executes x.dist cacheRow s t z ∧ z≤4+7*x.n ∧
      Cached x.n q (pre++(List.finRange x.n).map (x.dist a)) t := by
  let pts:=List.finRange x.n
  let I:=fun j (t:Store)=>Cached x.n q (pre++(pts.take j).map (x.dist a)) t ∧ t.ptrs 9=(a.val:ℤ)
  have st:I 0 s:=by simpa [I] using And.intro h ar
  obtain ⟨t,z,ex,tm,ans⟩:=for_run x.dist 0 11 12 x.n 3 (line insertOps) s I (by decide) (by decide)
    (by
      intro j u r v hr hu
      rcases hr with rfl|rfl <;> exact ⟨hu.1.ptr _ (by decide) (by decide) (by decide),hu.2⟩)
    h.points h.oneOK st (by
      intro j hj u hu idx
      have lt:j<pts.length:=by simpa [pts] using hj
      let b:=pts[j]
      have bval:b.val=j:=by simp [b,pts]
      have ins:=insert_ok x u q _ hu.1 a b hu.2 (by simpa only [bval] using idx)
      refine ⟨_,3,line_exec x.dist u insertOps,by rfl,?_,hu.2⟩
      simpa only [List.take_succ_eq_append_getElem lt,List.map_append,List.map_singleton,List.append_assoc,b] using ins)
  refine ⟨t,z,ex,by simpa [Nat.mul_comm] using tm,?_⟩
  have all:pts.take x.n=pts:=List.take_of_length_le (by simp [pts])
  simpa only [I,all,pts] using ans.1

theorem cache_all (x:World) (s:Store) (q:ℕ) (h:Cached x.n q [] s) :
    ∃t z,Executes x.dist loadCache s t z ∧ z≤4+x.n*(8+7*x.n) ∧ Cached x.n q (samples x) t := by
  let pts:=List.finRange x.n
  let I:=fun j (t:Store)=>Cached x.n q (rowsOf x (pts.take j)) t
  have start:I 0 s:=by simpa [I,rowsOf] using h
  obtain ⟨t,z,ex,tm,ans⟩:=for_run x.dist 0 9 10 x.n (4+7*x.n) cacheRow s I (by decide) (by decide)
    (by intro j u r v hr hu;rcases hr with rfl|rfl <;> exact hu.ptr _ (by decide) (by decide) (by decide))
    h.points h.oneOK start (by
      intro i hi u hu idx;have lt:i<pts.length:=by simpa [pts] using hi
      let a:=pts[i]
      have av:a.val=i:=by simp [a,pts]
      obtain ⟨t,z,ex,tm,res⟩:=cache_one x u q _ a hu (by simpa only [av] using idx)
      refine ⟨t,z,ex,tm,?_⟩
      simpa only [I,rowsOf,List.take_succ_eq_append_getElem lt,List.flatMap_append,List.flatMap_singleton,a] using res)
  have all:pts.take x.n=pts:=List.take_of_length_le (by simp [pts])
  have add:4+7*x.n+4=8+7*x.n:=by omega
  exact ⟨t,z,ex,by simpa only [add] using tm,by simpa only [I,all,pts,rowsOf,samples] using ans⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
open Compiler OracleQueries Relative.Machine
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

def rankTest := Cmd.seq (line [.realLoad 4 11,.realSub 4 0 4])
  (.ite (.realNonpos 4) .skip (.atom (.pointerInc 26)))
def countSmaller:=forCode 8 11 12 rankTest
def loadTarget:Op:=.realLoad 0 9

theorem test_run (n:ℕ) (d:Fin n→Fin n→ℝ) (s:Store) (v y:ℝ) (b:ℕ)
    (target:s.regs 0=v) (sample:s.mem (s.ptrs 11)=y) (acc:s.ptrs 26=(b:ℤ)) :
    ∃t z,Executes d rankTest s t z ∧ z≤5 ∧ t.ptrs 26=((b+(if y<v then 1 else 0):ℕ):ℤ):=by
  let ops:List Op:=[.realLoad 4 11,.realSub 4 0 4]
  let u:=perform d s ops
  have sub:u.regs 4=v-y:=by simp [u,ops,perform,Op.eval,target,sample]
  by_cases lt:y<v
  · have h:¬(Cond.realNonpos 4).test u:=by change ¬u.regs 4≤0;rw [sub];linarith
    exact ⟨_,_,.seq (line_exec d s ops) (.ite_false h (.atom _ _)),by decide,by simp [Op.eval,u,ops,perform,acc,lt]⟩
  · have h:(Cond.realNonpos 4).test u:=by change u.regs 4≤0;rw [sub];linarith
    exact ⟨_,_,.seq (line_exec d s ops) (.ite_true h (.skip _)),by decide,by simp [u,ops,perform,Op.eval,lt,acc]⟩

theorem count_run {n:ℕ} (d:Fin n→Fin n→ℝ) (ds:List ℝ) (s:Store) (v:ℝ) (b:ℕ)
    (hn:s.ptrs 8=(ds.length:ℤ)) (start:s.ptrs one=1) (hit:CacheAt ds s) (target:s.regs 0=v) (acc:s.ptrs 26=(b:ℤ)) :
    ∃t z,Executes d countSmaller s t z ∧ z≤4+ds.length*9 ∧ t.ptrs 26=((b+rank ds v:ℕ):ℤ):=by
  let I:=fun i (u:Store)=>u.ptrs 26=((b+rank (ds.take i) v:ℕ):ℤ) ∧ u.regs 0=v ∧ CacheAt ds u
  have init:I 0 s:=by simpa [I,rank] using And.intro acc (And.intro target hit)
  obtain ⟨t,z,ex,tm,ans⟩:=for_run d 8 11 12 ds.length 5 rankTest s I (by decide) (by decide)
    (by intro i u j k ev iu;rcases ev with rfl|rfl <;> exact iu) hn start init (by
      intro i hi u iu idx
      have rd:u.mem (u.ptrs 11)=ds[i]:=by rw [idx];exact iu.2.2 i hi
      obtain ⟨q,z,ex,tm,res⟩:=test_run n d u v ds[i] (b+rank (ds.take i) v) iu.2.1 rd iu.1
      have next:rank (ds.take (i+1)) v=rank (ds.take i) v+(if ds[i]<v then 1 else 0):=by
        rw [List.take_succ_eq_append_getElem hi];simp only [rank,List.filter_append,List.length_append]
        by_cases test:ds[i]<v <;> simp [test]
      refine ⟨q,z,ex,tm,?_,(preserves ex (.real 0) (by decide)).trans iu.2.1,?_⟩
      · rw [next,←Nat.add_assoc];exact res
      · intro j hj;exact (congrFun (preserves ex .mem (by decide)) _).trans (iu.2.2 j hj))
  exact ⟨t,z,ex,tm,by simpa only [List.take_length] using ans.1⟩

def selectBand := Cmd.seq (.atom (.realSub 4 0 1)) (.ite (.realNonpos 4) (.atom (.pointerConst 26 0))
  (.seq (.atom (.realSub 4 0 2)) (.ite (.realNonpos 4) (.atom (.pointerCopy 26 20))
    (.seq (.atom (.realSub 4 0 3)) (.ite (.realNonpos 4) (.atom (.pointerCopy 26 21)) (.atom (.pointerCopy 26 22)))))))

theorem branch_sub {n:ℕ} (d:Fin n→Fin n→ℝ) (s:Store) (r:ℕ) :
    (Cond.realNonpos 4).test ((Op.realSub 4 0 r).eval d s) ↔ s.regs 0 ≤ s.regs r := by
  simp [Cond.test,Op.eval,sub_nonpos]

theorem select_run {n:ℕ} (d:Fin n→Fin n→ℝ) (s:Store) (v R:ℝ) (H:ℕ) (tar:s.regs 0=v)
    (r2:s.regs 1=2*R) (r4:s.regs 2=4*R) (r8:s.regs 3=8*R)
    (p3:s.ptrs 20=3*(H:ℤ)) (p5:s.ptrs 21=5*(H:ℤ)) (p9:s.ptrs 22=9*(H:ℤ)) :
    ∃t z,Executes d selectBand s t z ∧ z≤10 ∧ t.ptrs 26=((band R v*H:ℕ):ℤ) := by
  let q:=(Op.realSub 4 0 1).eval d s
  let b:=(Op.realSub 4 0 2).eval d q
  have two:(Cond.realNonpos 4).test q ↔ v≤2*R:=by rw [branch_sub,tar,r2]
  have four:(Cond.realNonpos 4).test b ↔ v≤4*R:=by rw [branch_sub];change s.regs 0 ≤ s.regs 2 ↔ _;rw [tar,r4]
  have eight:(Cond.realNonpos 4).test ((Op.realSub 4 0 3).eval d b) ↔ v≤8*R:=by
    rw [branch_sub];change s.regs 0 ≤ s.regs 3 ↔ _;rw [tar,r8]
  by_cases t:v≤2*R
  · exact ⟨_,_,.seq (.atom _ _) (.ite_true (two.mpr t) (.atom _ _)),by decide,by simp [Op.eval,band,t]⟩
  by_cases f:v≤4*R
  · exact ⟨_,_,.seq (.atom _ _) (.ite_false (two.not.mpr t) (.seq (.atom _ _) (.ite_true (four.mpr f) (.atom _ _)))),
      by decide,by simp [Op.eval,q,band,t,f,p3]⟩
  by_cases e:v≤8*R
  · exact ⟨_,_,.seq (.atom _ _) (.ite_false (two.not.mpr t) (.seq (.atom _ _) (.ite_false (four.not.mpr f)
      (.seq (.atom _ _) (.ite_true (eight.mpr e) (.atom _ _)))))),by decide,by simp [Op.eval,q,b,band,t,f,e,p5]⟩
  · exact ⟨_,_,.seq (.atom _ _) (.ite_false (two.not.mpr t) (.seq (.atom _ _) (.ite_false (four.not.mpr f)
      (.seq (.atom _ _) (.ite_false (eight.not.mpr e) (.atom _ _)))))),by decide,by simp [Op.eval,q,b,band,t,f,e,p9]⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
open Compiler OracleQueries WindowCSP Relative.Machine
set_option autoImplicit false
set_option maxHeartbeats 1800000

def seekInit : List Op := [.pointerConst 7 1,.pointerCopy 14 3,.pointerConst 13 3,.pointerConst 15 2,.pointerAdd 15 0 15]
def seekOps : List Op := [.pointerSub 14 14 0,.pointerAdd 13 13 15]
def seek := Cmd.seq (line seekInit) (.whileDo (.pointerLE 0 14) (line seekOps))
def sceneOps : List Op := [.integerLoad 16 13,.pointerInc 13,.integerLoad 17 13,.distance 0 16 17,
  .realAdd 1 0 0,.realAdd 2 1 1,.realAdd 3 2 2,.pointerConst 8 0]
def setup := Cmd.seq seek (line sceneOps)
def Thresholds (R:ℝ) (s:Store) := s.regs 1=2*R ∧ s.regs 2=4*R ∧ s.regs 3=8*R

theorem seek_run (x:World) (s:Store) (r:ℕ) (points:s.ptrs 0=(x.n:ℤ)) (hn:0<x.n) (slot:s.ptrs 3=(r:ℤ)) :
    ∃t z,Executes x.dist seek s t z ∧ z≤7+4*(r/x.n) ∧ t.ptrs 13=(sceneBase x (r/x.n):ℤ) ∧ t.ptrs 7=1 := by
  let I:=fun i:ℕ=>fun q:Store=>q.ptrs 0=(x.n:ℤ) ∧ q.ptrs 14=(r:ℤ)-(i:ℤ)*(x.n:ℤ) ∧
    q.ptrs 13=3+(i:ℤ)*((x.n:ℤ)+2) ∧ q.ptrs 15=(x.n:ℤ)+2 ∧ q.ptrs 7=1
  let v:=perform x.dist s seekInit
  have first:I 0 v:=by simp [I,v,seekInit,perform,Op.eval,points,slot]
  have guard (i:ℕ) (hi:i≤r/x.n) (u:Store) (h:I i u) : (Cond.pointerLE 0 14).test u ↔ i<r/x.n:=by
    change u.ptrs 0 ≤ u.ptrs 14 ↔ _
    rw [h.1,h.2.1,Nat.lt_iff_add_one_le,Nat.le_div_iff_mul_le hn ]
    calc
      _ ↔ (((i+1)*x.n:ℕ):ℤ) ≤ (r:ℤ) := by push_cast;constructor <;> intro hh <;> nlinarith
      _ ↔ _ := Nat.cast_le
  obtain ⟨t,z,ex,tm,res⟩:=while_bounded x.dist _ _ (r/x.n) 2 I guard (by
    intro i hi u h
    refine ⟨_,2,line_exec x.dist u seekOps,by decide,?_⟩
    simp [I,seekOps,perform,Op.eval,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2] <;> ring_nf <;> simp) v first
  refine ⟨t,_,.seq (line_exec x.dist s seekInit) ex,?_,?_,res.2.2.2.2⟩
  · change 5+z≤_;omega
  · simpa [sceneBase] using res.2.2.1

theorem setup_run (x:World) (s:Store) (r:ℕ) (ready:Ready x s) (hn:0<x.n) (slot:s.ptrs 3=(r:ℤ))
    (live:r<x.rows*x.n) :
    ∃t z,Executes x.dist setup s t z ∧ z≤15+4*x.rows ∧ Cached x.n (s.queries+1) [] t ∧
      Thresholds (scale x (r/x.n)) t := by
  have h0:s.ptrs 0=(x.n:ℤ):=ready.1 .points
  obtain ⟨u,z,ex,tm,addr,oneOK⟩:=seek_run x s r h0 hn slot
  let base:=sceneBase x (r/x.n)
  have m:u.imem=s.imem:=preserves ex .imem (by decide)
  have v0:u.imem (u.ptrs 13)=x.mem base:=by rw [addr,m];exact ready.2 _
  have v1:u.imem (u.ptrs 13+1)=x.mem (base+1):=by rw [addr,m];exact_mod_cast ready.2 (base+1)
  have rd:MinSumFPT.oracleAnswer x.dist (u.imem (u.ptrs 13)) (u.imem (u.ptrs 13+1))=scale x (r/x.n):=by rw [v0,v1];rfl
  have hq:u.queries=s.queries:=preserves ex .queries (by decide)
  have pts:u.ptrs 0=(x.n:ℤ):=(preserves ex (.ptr 0) (by decide)).trans h0
  have bound:r/x.n<x.rows:=(Nat.div_lt_iff_lt_mul hn).mpr live
  refine ⟨_,_,.seq ex (line_exec x.dist u sceneOps),?_,?_,?_⟩
  · change z+8≤_;omega
  · refine ⟨?_,?_,?_,?_,?_⟩
    · simpa [sceneOps,perform,Op.eval] using pts
    · simpa [sceneOps,perform,Op.eval,one] using oneOK
    · simp [sceneOps,perform,Op.eval]
    · simp [sceneOps,perform,Op.eval,hq]
    · intro j hj;simp at hj
  · simp [Thresholds,sceneOps,perform,Op.eval,rd] <;> ring_nf <;> simp

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
open Compiler OracleQueries Relative.Machine
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000

structure Cfg (n:ℕ) (ds:List ℝ) (R:ℝ) (s:Store) : Prop where
  start : s.ptrs one=1
  bound : s.ptrs 8=(ds.length:ℤ)
  r2 : s.regs 1=2*R
  r4 : s.regs 2=4*R
  r8 : s.regs 3=8*R
  b3 : s.ptrs 20=3*(unit n:ℤ)
  b5 : s.ptrs 21=5*(unit n:ℤ)
  b9 : s.ptrs 22=9*(unit n:ℤ)
  stride : s.ptrs 25=64
  hit : CacheAt ds s

def cfgFields:List Field := [.ptr one,.ptr 8,.real 1,.real 2,.real 3,.ptr 20,.ptr 21,.ptr 22,.ptr 25,.mem]

theorem Cfg.keep {n k:ℕ} {ds:List ℝ} {R:ℝ} {s t:Store} {d:Fin k→Fin k→ℝ} {cmd:Cmd} {z:ℕ}
    (h:Cfg n ds R s) (ex:Executes d cmd s t z) (hc:cfgFields.all (fun f=>safe f cmd)=true) : Cfg n ds R t := by
  have pr (f:Field) (hf:f∈cfgFields) := preserves ex f (List.all_eq_true.mp hc f hf)
  have mm:t.mem=s.mem:=pr .mem (by simp [cfgFields])
  refine ⟨(pr (.ptr one) (by simp [cfgFields])).trans h.start,(pr (.ptr 8) (by simp [cfgFields])).trans h.bound,
    (pr (.real 1) (by simp [cfgFields])).trans h.r2,(pr (.real 2) (by simp [cfgFields])).trans h.r4,
    (pr (.real 3) (by simp [cfgFields])).trans h.r8,(pr (.ptr 20) (by simp [cfgFields])).trans h.b3,
    (pr (.ptr 21) (by simp [cfgFields])).trans h.b5,(pr (.ptr 22) (by simp [cfgFields])).trans h.b9,
    (pr (.ptr 25) (by simp [cfgFields])).trans h.stride,?_⟩
  intro j hj;rw [mm];exact h.hit j hj

theorem Cfg.outer {n j:ℕ} {ds:List ℝ} {R:ℝ} {s:Store} (h:Cfg n ds R s) (v:ℤ) (hj:j=9 ∨ j=10) :
    Cfg n ds R (setPtr s j v) := by
  rcases hj with rfl|rfl <;> exact ⟨h.start,h.bound,h.r2,h.r4,h.r8,h.b3,h.b5,h.b9,h.stride,h.hit⟩

def offsets:List Op:=[.pointerCopy 19 8,.pointerInc 19,.pointerAdd 23 19 19,.pointerAdd 20 23 19,
  .pointerAdd 23 23 23,.pointerAdd 21 23 19,.pointerAdd 23 23 23,.pointerAdd 22 23 19,
  .pointerConst 24 (cell 6 0),.pointerConst 25 64]

theorem offset_ok (x:World) (s:Store) (R:ℝ) (q:ℕ) (h:Cached x.n q (samples x) s)
    (hr:s.regs 1=2*R ∧ s.regs 2=4*R ∧ s.regs 3=8*R) :
    Cfg x.n (samples x) R (perform x.dist s offsets) ∧ (perform x.dist s offsets).ptrs 24=cell 6 0 := by
  refine ⟨⟨h.oneOK,h.next,hr.1,hr.2.1,hr.2.2,?_,?_,?_,by rfl,h.resident⟩,by rfl⟩ <;>
    simp [offsets,perform,Op.eval,h.next,samples_len,unit] <;> ring

def valueCode:=Cmd.seq (.atom loadTarget) (.seq selectBand countSmaller)
def writeOps:List Op:=[.integerStore 24 26,.pointerSub 24 24 25]
def rankOne:=Cmd.seq valueCode (line writeOps)
def rankAll:=forCode 8 9 10 rankOne

theorem value_run {n k:ℕ} (d:Fin k→Fin k→ℝ) (ds:List ℝ) (R:ℝ) (s:Store) (h:Cfg n ds R s)
    (i:ℕ) (hi:i<ds.length) (idx:s.ptrs 9=(i:ℤ)) :
    ∃t z,Executes d valueCode s t z ∧ z≤15+9*ds.length ∧ t.ptrs 26=(scalar n ds R ds[i]:ℤ) := by
  let u:=loadTarget.eval d s
  have read:u.regs 0=ds[i]:=by simp [u,loadTarget,Op.eval,idx,h.hit i hi]
  have hu:Cfg n ds R u:=h.keep (Executes.atom loadTarget s (d:=d)) (by decide)
  obtain ⟨v,y,ey,ty,acc⟩:=select_run d u ds[i] R (unit n) read hu.r2 hu.r4 hu.r8 hu.b3 hu.b5 hu.b9
  have hv:=hu.keep ey (by decide)
  have vv:v.regs 0=ds[i]:=(preserves ey (.real 0) (by decide)).trans read
  obtain ⟨t,z,ez,tz,ans⟩:=count_run d ds v ds[i] (band R ds[i]*unit n) hv.bound hv.start hv.hit vv acc
  exact ⟨t,_,.seq (.atom loadTarget s) (.seq ey ez),by omega,ans⟩

theorem cell_succ (i:ℕ) : cell 6 (i+1)=cell 6 i-64:=by unfold cell word;push_cast;ring
theorem cell_inj (i j:ℕ) (e:cell 6 i=cell 6 j) : i=j:=by unfold cell word at e;push_cast at e;omega

def Written (n:ℕ) (ds:List ℝ) (R:ℝ) (mem:ℤ→ℤ) (i:ℕ) (s:Store) :=
  s.ptrs 24=cell 6 i ∧ (∀j (hj:j<ds.length),j < i → s.imem (cell 6 j)=(scalar n ds R ds[j]:ℤ)) ∧
    ∀a:ℤ,(∀j:ℕ,a≠cell 6 j) → s.imem a=mem a

theorem write_run {n k:ℕ} (d:Fin k→Fin k→ℝ) (ds:List ℝ) (R:ℝ) (mem:ℤ→ℤ)
    (i:ℕ) (hi:i<ds.length) (s:Store) (cfg:Cfg n ds R s) (wr:Written n ds R mem i s) (idx:s.ptrs 9=(i:ℤ)) :
    ∃t z,Executes d rankOne s t z ∧ z≤17+9*ds.length ∧ Written n ds R mem (i+1) t := by
  obtain ⟨v,z,ex,tm,ans⟩:=value_run d ds R s cfg i hi idx
  let t:=perform d v writeOps
  have vm:v.imem=s.imem:=preserves ex .imem (by decide)
  have vp:v.ptrs 24=cell 6 i:=(preserves ex (.ptr 24) (by decide)).trans wr.1
  have vs:v.ptrs 25=64:=(preserves ex (.ptr 25) (by decide)).trans cfg.stride
  have im:t.imem=Function.update s.imem (cell 6 i) (scalar n ds R ds[i]:ℤ):=by simp [t,writeOps,perform,Op.eval,vm,vp,ans]
  refine ⟨t,_,.seq ex (line_exec d v writeOps),by change z+2≤_;omega,?_,?_,?_⟩
  · simp [t,writeOps,perform,Op.eval,vp,vs,cell_succ]
  · intro j hj ji;rw [im]
    by_cases eq:j=i
    · subst j;simp
    · rw [Function.update_of_ne (fun h=>eq (cell_inj j i h))];exact wr.2.1 j hj (by omega)
  · intro a ha;rw [im,Function.update_of_ne (ha i)];exact wr.2.2 a ha

theorem rank_all {n k:ℕ} (d:Fin k→Fin k→ℝ) (ds:List ℝ) (R:ℝ) (s:Store) (cfg:Cfg n ds R s) (base:s.ptrs 24=cell 6 0) :
    ∃t z,Executes d rankAll s t z ∧ z≤4+ds.length*(21+9*ds.length) ∧ Written n ds R s.imem ds.length t := by
  let I:=fun i (u:Store)=>Cfg n ds R u ∧ Written n ds R s.imem i u
  have first:I 0 s:=⟨cfg,base,by intro j hj h;omega,by intros;rfl⟩
  obtain ⟨t,z,ex,tm,ans⟩:=for_run d 8 9 10 ds.length (17+9*ds.length) rankOne s I (by decide) (by decide)
    (by intro i u j v hj hu;refine ⟨hu.1.outer v hj,?_⟩;rcases hj with rfl|rfl <;> exact hu.2)
    cfg.bound cfg.start first (by
      intro i hi u hu idx
      obtain ⟨v,y,ey,ty,w⟩:=write_run d ds R s.imem i hi u hu.1 hu.2 idx
      exact ⟨v,y,ey,ty,hu.1.keep ey (by decide),w⟩)
  exact ⟨t,z,ex,by simpa only [show 17+9*ds.length+4=21+9*ds.length by omega] using tm,ans.2⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
open Compiler OracleQueries Relative.Machine
set_option autoImplicit false

theorem sample_idx (x:World) (a b:Fin x.n) :
    ∃h:a.val*x.n+b.val<(samples x).length,(samples x)[a.val*x.n+b.val]=x.dist a b := by
  let pts:=List.finRange x.n
  have len (ls:List (Fin x.n)) : (rowsOf x ls).length=ls.length*x.n:=by
    induction ls with
    | nil=>simp [rowsOf]
    | cons c ls ih=>simpa [rowsOf,Nat.succ_mul,Nat.add_comm] using congrArg (x.n+·) ih
  have bound (j l:ℕ) (hj:j<l) : j*x.n+b.val<l*x.n:=by
    calc
      _< j*x.n+x.n:=Nat.add_lt_add_left b.isLt _
      _=(j+1)*x.n:=by ring
      _≤l*x.n:=Nat.mul_le_mul_right _ hj
  have get (ls:List (Fin x.n)) (j:ℕ) (hj:j<ls.length) :
      (rowsOf x ls)[j*x.n+b.val]'(by rw [len];exact bound j _ hj)=x.dist ls[j] b := by
    induction ls generalizing j with
    | nil=>simp at hj
    | cons c ls ih=>
      cases j with
      | zero=>
        simp only [Nat.zero_mul,Nat.zero_add,rowsOf,List.flatMap_cons,List.getElem_cons_zero]
        rw [List.getElem_append_left (by simpa using b.isLt)]
        simp
      | succ j=>
        have lt:j<ls.length:=by simpa using hj
        simp only [rowsOf,List.flatMap_cons,List.getElem_cons_succ]
        rw [List.getElem_append_right (by simp [Nat.succ_mul];omega)]
        have sub:(j+1)*x.n+b.val-((List.finRange x.n).map (x.dist c)).length=j*x.n+b.val:=by simp [Nat.succ_mul];omega
        simpa only [sub,rowsOf] using ih j lt
  have h:a.val<pts.length:=by simpa [pts] using a.isLt
  refine ⟨by rw [samples_len];exact bound _ _ a.isLt,?_⟩
  simpa [pts,rowsOf,samples] using get pts a.val h

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
open Compiler OracleQueries Relative.Machine WindowCSP
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def preprocessing:=Cmd.seq setup (.seq loadCache (.seq (line offsets) rankAll))

theorem prep_run (x:World) (s:Store) (ready:Ready x s) (hn:0<x.n) (r:ℕ)
    (slot:s.ptrs 3=(r:ℤ)) (live:r<x.rows*x.n) :
    ∃t z,Executes x.dist preprocessing s t z ∧ z≤200*(1+x.rows+(1+x.n*x.n)^2) ∧
      t.queries=s.queries+x.n*x.n+1 ∧ Ready x t ∧ (∀j<6,t.ptrs j=s.ptrs j) ∧
      (∀q:ℤ,(∀j:ℕ,q≠cell 6 j) → t.imem q=s.imem q) ∧ Prepared x (scale x (r/x.n)) t.imem := by
  let R:=scale x (r/x.n)
  obtain ⟨u,y,ey,byy,init,ths⟩:=setup_run x s r ready hn slot live
  obtain ⟨v,z,ez,bzz,cache⟩:=cache_all x u (s.queries+1) init
  have two:v.regs 1=2*R:=(preserves ez (.real 1) (by decide)).trans ths.1
  have four:v.regs 2=4*R:=(preserves ez (.real 2) (by decide)).trans ths.2.1
  have eight:v.regs 3=8*R:=(preserves ez (.real 3) (by decide)).trans ths.2.2
  let w:=perform x.dist v offsets
  have eo:Executes x.dist (line offsets) v w 10:=line_exec x.dist v offsets
  obtain ⟨cfg,base⟩:=offset_ok x v R _ cache ⟨two,four,eight⟩
  obtain ⟨t,k,ek,bkk,wr⟩:=rank_all x.dist (samples x) R w cfg base
  have ex:Executes x.dist preprocessing s t (y+(z+(10+k))):=.seq ey (.seq ez (.seq eo ek))
  have cost:y+(z+(10+k))≤200*(1+x.rows+(1+x.n*x.n)^2):=by
    rw [samples_len] at bkk
    have le:x.n≤x.n*x.n:=Nat.le_mul_of_pos_right _ hn
    nlinarith [Nat.zero_le (x.n^4)]
  have ptr (j:ℕ) (hj:j<6) : t.ptrs j=s.ptrs j:=by
    apply preserves ex (.ptr j);interval_cases j <;> decide
  have m:w.imem=s.imem:=Eq.trans (preserves eo .imem (by decide))
    (Eq.trans (preserves ez .imem (by decide)) (preserves ey .imem (by decide)))
  have frame (a:ℤ) (ha:∀j:ℕ,a≠cell 6 j) : t.imem a=s.imem a:=(wr.2.2 a ha).trans (congrFun m a)
  have rd:Ready x t:=by
    constructor
    · intro ax;rw [ptr ax.reg (by cases ax <;> decide)];exact ready.1 ax
    · intro j;rw [frame _ (by intro i;unfold cell word;push_cast;omega)];exact ready.2 j
  have q:t.queries=v.queries:=Eq.trans (preserves ek .queries (by decide)) (preserves eo .queries (by decide))
  refine ⟨t,_,ex,cost,?_,rd,ptr,frame,?_⟩
  · rw [q,cache.calls,samples_len];omega
  · intro a b;obtain ⟨hi,atIndex⟩:=sample_idx x a b
    simpa only [address,atIndex] using wr.2.1 (a.val*x.n+b.val) hi hi

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
theorem solution :
    ∃cmd:Cmd,∀(x:World) (s:Store),Ready x s → 0<x.n → ∀r:ℕ,s.ptrs 3=(r:ℤ) → r<x.rows*x.n →
    ∃t z,Executes x.dist cmd s t z ∧
      z≤200*(1+x.rows+(1+x.n*x.n)^2) ∧ t.queries=s.queries+x.n*x.n+1 ∧
      Ready x t ∧ (∀j<6,t.ptrs j=s.ptrs j) ∧
      (∀q:ℤ,(∀j:ℕ,q≠cell 6 j) → t.imem q=s.imem q) ∧ Prepared x (scale x (r/x.n)) t.imem := ⟨StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.preprocessing,StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Machine.prep_run⟩
