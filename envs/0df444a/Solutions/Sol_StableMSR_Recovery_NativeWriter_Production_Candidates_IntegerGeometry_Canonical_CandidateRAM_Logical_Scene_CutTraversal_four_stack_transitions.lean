-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.four_stack_transitions
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T12:48:37.259438+00:00
-- url     : https://prove2.me/submissions/ee809e7b-2708-449b-a464-e4c27d63e549

import Definitions.Def_StableMSR_CutStackMoves
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

section
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option linter.all false
set_option maxRecDepth 35000
set_option maxHeartbeats 4100000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 35000
theorem source_loop {N:ℕ} {input:ℤ → ℤ} (ix last n cap:ℕ) (body:Program) (P:ℕ→State→Prop) (ne:ix≠last)
    (step:∀i<n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1)))
    (i rem:ℕ) (len:i+rem=n) (s:State) (start:P i s) (idx:s.reg ix=(i:ℤ)) (lim:s.reg last=(n:ℤ)-1) :
    ∃t k,Executes N input (.loop ix last (chain [body,.op (.regular (.inc ix))])) s t k ∧ k≤1+rem*(cap+5) ∧ P n t :=by
  induction rem generalizing i s with
  | zero=>
    have eq:i=n:=by omega
    exact ⟨s,1,.stop (by rw [idx,lim];omega),by omega,eq ▸ start⟩
  | succ r ih=>
    have lt:i<n:=by omega
    obtain ⟨u,k,ex,tim,idx',lim',next⟩:=step i lt s start idx lim
    let v:=u.assign ix (u.reg ix+1)
    have vi:v.reg ix=((i+1:ℕ):ℤ):=by simp [v,State.assign,idx',idx]
    have vl:v.reg last=(n:ℤ)-1:=by simp [v,State.assign,Ne.symm ne,lim',lim]
    obtain ⟨t,z,more,tm,out⟩:=ih (i+1) (by omega) v next vi vl
    have full:Executes N input (chain [body,.op (.regular (.inc ix))]) s v (1+k+(1+1+1)):=.seq ex (.seq (.op rfl) (.skip _))
    exact ⟨t,_,.more (by rw [idx,lim];omega) full more,by rw [Nat.succ_mul];omega,out⟩

def forSetup (ix last len:ℕ) (s:State) := let u:=s.assign ix 0; let v:=u.assign last (u.reg len);v.assign last (v.reg last-1)
theorem source_for {N:ℕ} {input:ℤ → ℤ} (ix last len n cap:ℕ) (body:Program) (P:ℕ→State→Prop)
    (ne:ix≠last) (dis:len≠ix) (s:State) (size:s.reg len=(n:ℤ))
    (start:P 0 (forSetup ix last len s))
    (step:∀i<n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1))) :
    ∃t k,Executes N input (forCount ix last len body) s t k ∧ k≤9+n*(cap+5) ∧ P n t :=by
  let u:=forSetup ix last len s
  have fi:u.reg ix=0:=by simp [u,forSetup,State.assign,ne]
  have last':u.reg last=(n:ℤ)-1:=by simp [u,forSetup,State.assign,dis,size]
  obtain ⟨t,z,loop,tm,out⟩:=source_loop ix last n cap body P ne step 0 n (by omega) u start fi last'
  refine ⟨t,_,.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq loop (.skip _)))),by omega,out⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
inductive PrefixRun (N:ℕ) (input:ℤ → ℤ) : List Program → State → State → ℕ → Prop where
  | nil (s:State) : PrefixRun N input [] s s 0
  | cons {p ps s u t a z} : Executes N input p s u a → PrefixRun N input ps u t z →
    PrefixRun N input (p::ps) s t (1+a+z)
theorem PrefixRun.continue {N input ps s t z} (h:PrefixRun N input ps s t z)
    (q:Program) {u k} (tail:Executes N input q t u k):
    Executes N input (ps.foldr Program.seq q) s u (z+k):=by
  induction h with
  | nil=>simpa using tail
  | cons run _ ih=>
    simpa [Nat.add_assoc] using Executes.seq run (ih tail)
theorem PrefixRun.finish {N input ps s t z} (h:PrefixRun N input ps s t z):
    Executes N input (chain ps) s t (z+1):=h.continue .skip (.skip t)
end Logical
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
def evalLine (n:ℕ) (m:ℤ → ℤ) : Program → State → Option (State×ℕ)
  | .skip,s=>some (s,1)
  | .op o,s=>o.next n m s
  | .seq p q,s=>do
    let (u,a)←evalLine n m p s
    let (t,b)←evalLine n m q u
    pure (t,1+a+b)
  | .cond i j p q,s=>do
    let (t,b)←if s.reg i ≤ s.reg j then evalLine n m p s else evalLine n m q s
    pure (t,1+b)
  | .loop _ _ _,_=>none
theorem evalLine_sound {n m} (p:Program) (s t:State) (k:ℕ) (ex:evalLine n m p s=some (t,k)):
    Executes n m p s t k:=by
  induction p generalizing s t k with
  | skip=>obtain ⟨rfl,rfl⟩:=Option.some.inj ex;exact .skip _
  | op=>exact .op ex
  | loop=>contradiction
  | seq p q a b=>
    cases h:evalLine n m p s with
    | none=>simp [evalLine,h] at ex
    | some z=>
      obtain ⟨u,au⟩:=z
      cases j:evalLine n m q u with
      | none=>simp [evalLine,h,j] at ex
      | some v=>obtain ⟨v,bu⟩:=v;simp [evalLine,h,j] at ex;obtain ⟨rfl,rfl⟩:=ex
                exact .seq (a _ _ _ h) (b _ _ _ j)
  | cond i j p q a b=>
    by_cases g:s.reg i ≤ s.reg j
    · cases h:evalLine n m p s with
      | none=>simp [evalLine,g,h] at ex
      | some z=>obtain ⟨u,au⟩:=z;simp [evalLine,g,h] at ex;obtain ⟨rfl,rfl⟩:=ex;exact .yes g (a _ _ _ h)
    · cases h:evalLine n m q s with
      | none=>simp [evalLine,g,h] at ex
      | some z=>obtain ⟨u,au⟩:=z;simp [evalLine,g,h] at ex;obtain ⟨rfl,rfl⟩:=ex;exact .no g (b _ _ _ h)

def writesOp (j:ℕ) : Operation → Bool
  | .regular (.store _ _)|.save _ _ _=>false
  | .regular (.set d _)|.regular (.copy d _)|.regular (.add d _ _)|.regular (.sub d _ _)|
    .regular (.inc d)|.regular (.dec d)|.regular (.load d _)|.multiply d _ _|.divide _ d _ _|
    .fetch d _ _|.shift d _ _=>j==d
  | .alloc d _=>j==d || j==8
  | .output=>j==82
def writesReg (j:ℕ) : Program → Bool
  | .skip=>false | .op o=>writesOp j o | .seq p q|.cond _ _ p q=>writesReg j p || writesReg j q
  | .loop _ _ p=>writesReg j p
theorem op_preserves {n input s t k} (o:Operation) (j:ℕ) (frame:writesOp j o=false)
    (ex:o.next n input s=some (t,k)):t.reg j=s.reg j:=by
  cases o with
  | regular o=>
    cases o <;> simp [writesOp] at frame <;> simp only [Operation.next,regularNext] at ex <;>
      (try split at ex) <;> (try contradiction) <;> obtain ⟨rfl,rfl⟩:=Option.some.inj ex <;> simp [State.assign,frame]
  | multiply|divide|shift|fetch|save|alloc|output=>
    simp [writesOp] at frame
    simp only [Operation.next] at ex
    (try split at ex) <;> (try contradiction) <;> obtain ⟨rfl,rfl⟩:=Option.some.inj ex <;>
      simp_all [State.assign,State.clear,State.save]
theorem Executes.preserves {n input p s t k} (ex:Executes n input p s t k) (j:ℕ) (off:writesReg j p=false):
    t.reg j=s.reg j:=by
  induction ex with
  | skip|stop=>rfl
  | op h=>exact op_preserves _ _ off h
  | seq _ _ ih jh=>obtain ⟨a,b⟩:=Bool.or_eq_false_iff.mp off;exact (jh b).trans (ih a)
  | yes _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).1
  | no _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).2
  | more _ _ _ ih jh=>exact (jh off).trans (ih off)
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open scoped Classical
theorem splitChain {N input} (ps:List Program) {s t:State} {k:ℕ} (ex:Executes N input (chain ps) s t k) :
    ∃z,PrefixRun N input ps s t z ∧ k=z+1:=by
  induction ps generalizing s t k with
  | nil=>cases ex;exact ⟨0,.nil _,rfl⟩
  | cons p ps ih=>
    change Executes N input (.seq p (chain ps)) s t k at ex
    cases ex with
    | seq left right=>
      obtain ⟨z,e,h⟩:=ih right
      exact ⟨_,.cons left e,by omega⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM



end
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option linter.all false
set_option maxRecDepth 35000
set_option maxHeartbeats 4100000
set_option autoImplicit false


namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open SingleCircuit TightLanguage SeparatorLevels
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 35000

private def header : List Program := [
  .op (.fetch 1168 262 263), .op (.regular (.copy 265 1168)),
  .op (.regular (.set 1171 0)), .op (.regular (.copy 266 1171)), .op (.regular (.set 1174 0)),
  .cond 263 1174 (.op (.regular (.set 1172 0))) (.op (.regular (.set 1172 1))),
  .cond 6 1172 (chain [.op (.regular (.set 1180 1)), .op (.regular (.sub 1178 263 1180)),
    .op (.fetch 1176 261 1178), .op (.regular (.set 1181 1)), .op (.regular (.add 1175 1176 1181)),
    .op (.regular (.copy 266 1175))]) .skip,
  .cond 67 263 (.op (.regular (.set 1183 0))) (.op (.regular (.set 1183 1))),
  .op (.regular (.copy 1182 1183)),
  .cond 6 1182 (chain [.cond 266 265 (.op (.regular (.set 1186 1))) (.op (.regular (.set 1186 0))),
    .op (.regular (.copy 1182 1186))]) .skip]
private def decrement : List Program := [
  .op (.regular (.set 1194 1)), .op (.regular (.sub 1192 265 1194)),
  .op (.save 262 263 1192), .op (.fetch 1195 71 265)]
private def pushList : List Program := [
  .op (.save 261 263 265), .op (.regular (.set 1205 1)), .op (.save 260 265 1205),
  .op (.regular (.set 1208 1)), .op (.regular (.add 1206 263 1208)), .op (.regular (.copy 263 1206)),
  .op (.regular (.set 1214 1)), .op (.regular (.sub 1212 64 1214)), .op (.save 262 263 1212),
  .op (.regular (.copy 240 259)), .op (.regular (.copy 241 260)), .op (.regular (.copy 242 261)),
  .op (.regular (.copy 243 263))]
private def pushReturn : Program := .op (.regular (.copy 1215 258))
private def descend := chain (pushList++[src_visit,pushReturn])
private def advance := chain (decrement++[.cond 6 1195 descend .skip])
private def retreat : Program := chain [
  .op (.regular (.set 1222 0)),
  .cond 263 1222 (.cond 1222 263 (.op (.regular (.set 1220 1))) (.op (.regular (.set 1220 0))))
    (.op (.regular (.set 1220 0))),
  .cond 6 1220 (chain [.op (.regular (.set 1223 1)), .op (.regular (.copy 264 1223))])
    (chain [.op (.regular (.set 1226 1)), .op (.regular (.sub 1224 263 1226)), .op (.regular (.copy 263 1224)),
      .op (.fetch 1229 261 263), .op (.regular (.set 1232 0)), .op (.save 260 1229 1232)])]
private def resetFlag : Program := .cond 6 264 (.op (.regular (.set 1166 0))) (.op (.regular (.set 1166 1)))
private def dispatch : Program := .cond 6 1182 advance retreat
private lemma body_code : loopBody=chain (header++[dispatch,resetFlag]) := rfl

private def layoutReg (j : ℕ) := j ≤ 82 ∨ (259 ≤ j ∧ j ≤ 262)
private structure Frame (s t : State) : Prop where
  reg : ∀j,layoutReg j → t.reg j=s.reg j
  out : t.output=s.output
  closed : t.closed=s.closed

private lemma persistent {z s t : State} (old : Between z s) (f : Frame s t)
    (cells : ∀j<(z.reg 8).toNat,t.heap j=s.heap j) : Between z t := by
  exact ⟨fun j h=>(f.reg j (by unfold layoutReg;omega)).trans (old.control j h),
    (f.reg 8 (.inl (by decide))) ▸ old.cursor,fun j h=>(cells j h).trans (old.tables j h),
    (f.reg 82 (.inl (by decide))).trans (old.count.trans (congrArg (fun o : List Instr=>(o.length:ℤ)) f.out.symm)),
    f.closed.trans old.available⟩

private lemma unchanged {n level base z c ix s t} (im : StackAt n level base z c ix s)
    (f : Frame s t) (depth : t.reg 263=s.reg 263) (done_ : t.reg 264=s.reg 264)
    (go : t.reg 1166=s.reg 1166) (heap : t.heap=s.heap) : StackAt n level base z c ix t := by
  exact ⟨persistent im.between f (fun j _=>congrFun heap j),
    (f.reg 259 (.inr (by decide))).trans im.levelReg,(f.reg 260 (.inr (by decide))).trans im.bitmap,
    (f.reg 261 (.inr (by decide))).trans im.vector,(f.reg 262 (.inr (by decide))).trans im.stack,
    depth.trans im.depth,done_.trans im.doneFlag,go.trans im.running,(f.reg 8 (.inl (by decide))) ▸ im.reserved,
    fun q h=>(congrFun heap _).trans (im.bits q h),by rw [heap];exact im.ancestors,(congrFun heap _).trans im.pending⟩

private lemma plusAddr (a b : ℕ) : ((a:ℤ)+b).toNat=a+b := by omega
private lemma plusPos (a b : ℕ) : 0 ≤ (a:ℤ)+b := by omega

private lemma inspect (d : Instance) (w level base : ℕ) (m : ℤ→ℤ) (z s : State) (c : List ℕ) (ix : ℤ)
    (data : TraversalData d w z) (im : StackAt d.n level base z c ix s) :
    ∃t k, Executes d.n m (chain header) s t k ∧ k ≤ 190 ∧ StackAt d.n level base z c ix t ∧
      t.reg 265=ix ∧ t.reg 1182=(if canExtend w c ix then 1 else 0) ∧ t.output=s.output := by
  classical
  have one := (im.between.control 6 (.inl rfl)).trans data.one
  have width := (im.between.control 67 (.inr (.inr (by decide)))).trans data.width
  let vec:=base+d.n
  let stk:=vec+d.n
  have vp : s.reg 261=(vec:ℤ) := im.vector
  have sp : s.reg 262=(stk:ℤ) := im.stack
  have raw : ∃u k,evalLine d.n m (chain header) s=some (u,k) ∧ k ≤ 190 ∧ u.reg 265=ix ∧
      u.reg 1182=(if canExtend w c ix then 1 else 0) ∧ u.heap=s.heap ∧ u.output=s.output ∧ u.closed=s.closed := by
    rcases List.eq_nil_or_concat c with rfl | ⟨cs,q,h⟩
    · have dep : s.reg 263=0 := im.depth
      have top : s.heap stk=ix := by simpa [stk,vec] using im.pending
      by_cases w0 : w=0 <;> by_cases nonneg : 0 ≤ ix <;>
        simp [header,chain,evalLine,Operation.next,regularNext,State.assign,one,width,sp,dep,top,canExtend,lower,w0,nonneg]
    · rw [List.concat_eq_append] at h
      subst c
      let i:=cs.length
      have dep : s.reg 263=(i:ℤ)+1 := by simpa [i] using im.depth
      have top : s.heap (stk+(i+1))=ix := by simpa [stk,vec,i] using im.pending
      have last : s.heap (vec+i)=(q:ℤ) := by
        have := (im.ancestors i (by simp [i])).1;simpa [vec,i] using this
      have nonneg : 0 ≤ (stk:ℤ)+((i:ℤ)+1) := by omega
      have addr : ((stk:ℤ)+((i:ℤ)+1)).toNat=stk+(i+1) := by omega
      have depPos : ¬(i:ℤ)+1 ≤ 0 := by omega
      by_cases capped : w ≤ i+1 <;> by_cases above : (q:ℤ)+1 ≤ ix <;>
        simp [header,chain,evalLine,Operation.next,regularNext,State.assign,one,width,vp,sp,dep,top,last,canExtend,lower,
          nonneg,addr,depPos,plusAddr,plusPos,show ((w:ℤ) ≤ (i:ℤ)+1) ↔ w ≤ i+1 by omega,capped,above,show cs.length=i from rfl] <;> omega
  obtain ⟨t,k,ev,kt,top,extend,heap,out,cl⟩:=raw
  have run:=evalLine_sound _ _ _ _ ev
  have f : Frame s t := ⟨by intro j hj;apply run.preserves
                            simp [header,chain,writesReg,writesOp];unfold layoutReg at hj;omega,out,cl⟩
  exact ⟨t,k,run,kt,unchanged im f (run.preserves _ (by decide)) (run.preserves _ (by decide))
    (run.preserves _ (by decide)) heap,top,extend,out⟩

private lemma decrement_at (d : Instance) (w level base q : ℕ) (m : ℤ→ℤ) (z s : State) (c : List ℕ)
    (data : TraversalData d w z) (below : (z.reg 8).toNat ≤ base)
    (im : StackAt d.n level base z c (q:ℤ) s) (top : s.reg 265=(q:ℤ)) (qn : q<d.n) :
    ∃t k, Executes d.n m (chain decrement) s t k ∧ k ≤ 140 ∧
      StackAt d.n level base z c ((q:ℤ)-1) t ∧ t.reg 1195=(if d.active q then 1 else 0) ∧ t.output=s.output := by
  obtain ⟨addr,where_,cells⟩:=data.active
  have ptr:=(im.between.control 71 (.inr (.inr (by decide)))).trans where_
  obtain ⟨before,bit⟩:=cells q qn
  let stk:=base+d.n+d.n
  have sp : s.reg 262=(stk:ℤ) := im.stack
  have small : addr+q ≠ stk+c.length := by dsimp [stk];omega
  have val: s.heap (addr+q)=if d.active q then 1 else 0 := (im.between.tables _ before).trans bit
  have raw : ∃t k,evalLine d.n m (chain decrement) s=some (t,k) ∧ k ≤ 140 ∧
      t.heap=Function.update s.heap (stk+c.length) ((q:ℤ)-1) ∧ t.reg 1195=(if d.active q then 1 else 0) ∧
      t.output=s.output ∧ t.closed=s.closed := by
    simp [decrement,chain,evalLine,Operation.next,regularNext,State.assign,State.save,ptr,sp,im.depth,top,
      plusAddr,plusPos,small,val]
  obtain ⟨t,k,ev,kt,heap,flag,out,cl⟩:=raw
  have run:=evalLine_sound _ _ _ _ ev
  have f : Frame s t := ⟨by intro j hj;apply run.preserves
                            simp [decrement,chain,writesReg,writesOp];unfold layoutReg at hj;omega,out,cl⟩
  have off (j : ℕ) (ne : j≠stk+c.length) : t.heap j=s.heap j := by rw [heap,Function.update_of_ne ne]
  refine ⟨t,k,run,kt,⟨persistent im.between f (fun j hj=>off _ (by dsimp [stk];omega)),
    (run.preserves 259 (by decide)).trans im.levelReg,(run.preserves 260 (by decide)).trans im.bitmap,
    (run.preserves 261 (by decide)).trans im.vector,(run.preserves 262 (by decide)).trans im.stack,
    (run.preserves 263 (by decide)).trans im.depth,(run.preserves 264 (by decide)).trans im.doneFlag,
    (run.preserves 1166 (by decide)).trans im.running,(run.preserves 8 (by decide)) ▸ im.reserved,
    fun j hj=>(off _ (by dsimp [stk];omega)).trans (im.bits j hj),?_,?_⟩,flag,out⟩
  · intro i hi;obtain ⟨v,n⟩:=im.ancestors i hi
    exact ⟨(off _ (by dsimp [stk];omega)).trans v,(off _ (by dsimp [stk];omega)).trans n⟩
  · rw [heap];exact Function.update_self ..

private lemma normal_flag (d : Instance) (w level base : ℕ) (m : ℤ→ℤ) (z s : State) (c : List ℕ) (ix : ℤ)
    (data : TraversalData d w z) (im : StackAt d.n level base z c ix s) :
    ∃t, Executes d.n m resetFlag s t 2 ∧ StackAt d.n level base z c ix t ∧ t.output=s.output := by
  let t:=s.assign 1166 1
  have one:=(im.between.control 6 (.inl rfl)).trans data.one
  have run : Executes d.n m resetFlag s t 2 := by
    apply evalLine_sound
    simp [resetFlag,evalLine,Operation.next,regularNext,State.assign,t,one,im.doneFlag]
  refine ⟨t,run,unchanged im ⟨?_,rfl,rfl⟩ (by rfl) (by rfl) (by simp [t,State.assign,im.running]) rfl,rfl⟩
  intro j good
  exact run.preserves _ (by simp [resetFlag,writesReg,writesOp];unfold layoutReg at good;omega)

private lemma push_at (d : Instance) (w level base q : ℕ) (m : ℤ→ℤ) (z s : State) (c : List ℕ)
    (data : TraversalData d w z) (below : (z.reg 8).toNat ≤ base)
    (im : StackAt d.n level base z c ((q:ℤ)-1) s) (top : s.reg 265=(q:ℤ))
    (qn : q<d.n) (cn : c.length<d.n) :
    ∃t k, Executes d.n m (chain pushList) s t k ∧ k ≤ 235 ∧
      StackAt d.n level base z (c++[q]) ((d.n:ℤ)-1) t ∧ CutInput d.n level (c++[q]) t ∧ t.output=s.output := by
  let vec:=base+d.n
  let stk:=vec+d.n
  let i:=c.length
  have vp : s.reg 261=(vec:ℤ):=im.vector
  have sp : s.reg 262=(stk:ℤ):=im.stack
  have cp : s.reg 263=(i:ℤ):=im.depth
  have size := (im.between.control 64 (.inr (.inr (by decide)))).trans data.size
  have ap : ((stk:ℤ)+((i:ℤ)+1)).toNat=stk+(i+1) := by omega
  have pp : 0 ≤ (stk:ℤ)+((i:ℤ)+1) := by omega
  let mem := Function.update (Function.update (Function.update s.heap (vec+i) (q:ℤ)) (base+q) 1)
    (stk+(i+1)) ((d.n:ℤ)-1)
  have raw : ∃t k,evalLine d.n m (chain pushList) s=some (t,k) ∧ k ≤ 235 ∧ t.heap=mem ∧
      t.reg 263=(i:ℤ)+1 ∧ t.reg 240=(level:ℤ) ∧ t.reg 241=(base:ℤ) ∧ t.reg 242=(vec:ℤ) ∧
      t.reg 243=(i:ℤ)+1 ∧ t.output=s.output ∧ t.closed=s.closed := by
    simp [pushList,chain,evalLine,Operation.next,regularNext,State.assign,State.save,cp,vp,sp,top,
      im.bitmap,size,im.levelReg,plusAddr,plusPos,ap,pp,mem]
  obtain ⟨t,k,ev,kt,heap,dep,lev,bm,vp',len,out,cl⟩:=raw
  have run:=evalLine_sound _ _ _ _ ev
  have f : Frame s t := ⟨by intro j hj;apply run.preserves
                            simp [pushList,chain,writesReg,writesOp];unfold layoutReg at hj;omega,out,cl⟩
  have off (j : ℕ) (a : j≠stk+(i+1)) (b : j≠base+q) (v : j≠vec+i) :
      t.heap j=s.heap j := by simp [heap,mem,a,b,v,Function.update_of_ne]
  have vv : t.heap (vec+i)=(q:ℤ) := by
    simp [heap,mem,Function.update_of_ne (show vec+i≠stk+(i+1) by dsimp [stk];omega),
      Function.update_of_ne (show vec+i≠base+q by dsimp [vec];omega)]
  have bit : t.heap (base+q)=1 := by
    simp [heap,mem,Function.update_of_ne (show base+q≠stk+(i+1) by dsimp [stk,vec];omega)]
  have next : t.heap (stk+(i+1))=(d.n:ℤ)-1 := by simp [heap,mem]
  have rs : StackAt d.n level base z (c++[q]) ((d.n:ℤ)-1) t := by
    refine ⟨persistent im.between f (fun j hj=>off _ (by dsimp [stk,vec];omega) (by omega) (by dsimp [vec];omega)),
      (run.preserves 259 (by decide)).trans im.levelReg,(run.preserves 260 (by decide)).trans im.bitmap,
      (run.preserves 261 (by decide)).trans im.vector,(run.preserves 262 (by decide)).trans im.stack,
      by simpa [i] using dep,(run.preserves 264 (by decide)).trans im.doneFlag,
      (run.preserves 1166 (by decide)).trans im.running,(run.preserves 8 (by decide)) ▸ im.reserved,
      ?_,?_,by simpa [stk,vec,i] using next⟩
    · intro j hj
      by_cases eq : j=q
      · subst j;simpa using bit
      · rw [off _ (by dsimp [stk,vec];omega) (by omega) (by dsimp [vec];omega),im.bits j hj]
        simp [eq]
    · intro j hj
      by_cases lt : j<c.length
      · rw [List.getElem_append_left lt]
        obtain ⟨old,nextJ⟩:=im.ancestors j lt
        exact ⟨(off _ (by dsimp [stk,vec,i];omega) (by omega) (by dsimp [vec,i];omega)).trans old,
          (off _ (by dsimp [stk,vec,i];omega) (by omega) (by dsimp [vec,i];omega)).trans nextJ⟩
      · have eq : j=c.length := by simp at hj;omega
        subst j
        have parent : t.heap (stk+i)=(q:ℤ)-1 := (off _ (by omega) (by dsimp [stk,vec];omega)
          (by dsimp [stk,vec];omega)).trans im.pending
        simpa [i,stk,vec] using And.intro vv parent
  have reserved:=rs.reserved
  refine ⟨t,k,run,kt,rs,⟨lev,by simpa [i] using len,base,vec,bm,vp',by omega,
    by dsimp [vec];omega,rs.bits,fun j hj=>(rs.ancestors j hj).1⟩,out⟩

private lemma after_call {d : Instance} {level base : ℕ} {m : ℤ→ℤ} {z s t : State} {c : List ℕ} {ix : ℤ} {k : ℕ}
    (im : StackAt d.n level base z c ix s) (len : c.length ≤ d.n)
    (ex : Executes d.n m src_visit s t k) (keep : Between s t) : StackAt d.n level base z c ix t := by
  have lim:=im.reserved
  have za:=im.between
  refine ⟨⟨fun j h=>(keep.control j h).trans (za.control j h),za.cursor.trans keep.cursor,
    fun j hj=>(keep.tables j (by have:=za.cursor;omega)).trans (za.tables j hj),keep.count,keep.available⟩,
    (ex.preserves 259 (by decide)).trans im.levelReg,(ex.preserves 260 (by decide)).trans im.bitmap,
    (ex.preserves 261 (by decide)).trans im.vector,(ex.preserves 262 (by decide)).trans im.stack,
    (ex.preserves 263 (by decide)).trans im.depth,(ex.preserves 264 (by decide)).trans im.doneFlag,
    (ex.preserves 1166 (by decide)).trans im.running,lim.trans keep.cursor,?_,?_,?_⟩
  · exact fun j hj=>(keep.tables _ (by omega)).trans (im.bits j hj)
  · intro j hj
    exact ⟨(keep.tables _ (by omega)).trans (im.ancestors j hj).1,
      (keep.tables _ (by omega)).trans (im.ancestors j hj).2⟩
  · exact (keep.tables _ (by omega)).trans im.pending

private lemma pop_at (d : Instance) (w level base q : ℕ) (m : ℤ→ℤ) (z s : State) (c : List ℕ) (ix : ℤ)
    (data : TraversalData d w z) (below : (z.reg 8).toNat ≤ base)
    (im : StackAt d.n level base z (c++[q]) ix s) (qn : q<d.n) (cn : c.length<d.n) (fresh : q∉c) :
    ∃t k, Executes d.n m retreat s t k ∧ k ≤ 157 ∧ StackAt d.n level base z c ((q:ℤ)-1) t ∧ t.output=s.output := by
  let vec:=base+d.n
  let i:=c.length
  have vp : s.reg 261=(vec:ℤ):=im.vector
  have dep : s.reg 263=(i:ℤ)+1 := by simpa [i] using im.depth
  have one := (im.between.control 6 (.inl rfl)).trans data.one
  have last : s.heap (vec+i)=(q:ℤ) ∧ s.heap (vec+d.n+i)=(q:ℤ)-1 := by
    simpa [vec,i] using im.ancestors i (by simp [i])
  have raw : ∃t k,evalLine d.n m retreat s=some (t,k) ∧ k ≤ 157 ∧
      t.heap=Function.update s.heap (base+q) 0 ∧ t.reg 263=(i:ℤ) ∧ t.output=s.output ∧ t.closed=s.closed := by
    simp [retreat,chain,evalLine,Operation.next,regularNext,State.assign,State.save,dep,vp,im.bitmap,one,
      show ¬((i:ℤ)+1 ≤ 0) by omega,plusAddr,plusPos,last.1]
  obtain ⟨t,k,ev,kt,heap,depth,out,cl⟩:=raw
  have run:=evalLine_sound _ _ _ _ ev
  have f : Frame s t := ⟨by intro j hj;apply run.preserves
                            simp [retreat,chain,writesReg,writesOp];unfold layoutReg at hj;omega,out,cl⟩
  have off (j : ℕ) (ne : j≠base+q) : t.heap j=s.heap j := by simp [heap,Function.update_of_ne ne]
  refine ⟨t,k,run,kt,⟨persistent im.between f (fun j hj=>off _ (by omega)),
    (run.preserves 259 (by decide)).trans im.levelReg,(run.preserves 260 (by decide)).trans im.bitmap,
    (run.preserves 261 (by decide)).trans im.vector,(run.preserves 262 (by decide)).trans im.stack,
    depth,?_,(run.preserves 1166 (by decide)).trans im.running,(run.preserves 8 (by decide)) ▸ im.reserved,
    ?_,?_,(off _ (by omega)).trans last.2⟩,out⟩
  · have eq : t.reg 264=s.reg 264 := by
      have := ev
      simp [retreat,chain,evalLine,Operation.next,regularNext,State.assign,State.save,dep,vp,im.bitmap,one,
        show ¬((i:ℤ)+1 ≤ 0) by omega,plusAddr,plusPos,last.1] at this
      rw [←this.1];simp
    exact eq.trans im.doneFlag
  · intro j hj
    by_cases eq : j=q
    · subst j;simp [heap,fresh]
    · rw [off _ (by omega),im.bits j hj];simp [eq]
  · intro j hj
    have old := im.ancestors j (by simp;omega)
    rw [List.getElem_append_left hj] at old
    exact ⟨(off _ (by omega)).trans old.1,(off _ (by omega)).trans old.2⟩

private lemma stop_at (d : Instance) (w level base : ℕ) (m : ℤ→ℤ) (z s : State) (ix : ℤ)
    (data : TraversalData d w z) (im : StackAt d.n level base z [] ix s) :
    ∃t k, Executes d.n m retreat s t k ∧ k ≤ 20 ∧ t.reg 264=1 ∧ t.reg 6=1 ∧ Between z t ∧ t.output=s.output := by
  have one := (im.between.control 6 (.inl rfl)).trans data.one
  have depth : s.reg 263=0:=im.depth
  have raw : ∃t k,evalLine d.n m retreat s=some (t,k) ∧ k ≤ 20 ∧ t.reg 264=1 ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    simp [retreat,chain,evalLine,Operation.next,regularNext,State.assign,depth,one]
  obtain ⟨t,k,ev,kt,flag,heap,out,cl⟩:=raw
  have run:=evalLine_sound _ _ _ _ ev
  have f : Frame s t := ⟨by intro j hj;apply run.preserves
                            simp [retreat,chain,writesReg,writesOp];unfold layoutReg at hj;omega,out,cl⟩
  exact ⟨t,k,run,kt,flag,(run.preserves 6 (by decide)).trans one,persistent im.between f (fun j _=>congrFun heap j),out⟩

private lemma run_normal {d : Instance} {w level base : ℕ} {m : ℤ→ℤ} {z s t u : State} {k j : ℕ}
    {c : List ℕ} {ix : ℤ} (data : TraversalData d w z)
    (head_ : Executes d.n m (chain header) s t k) (act : Executes d.n m dispatch t u j)
    (image : StackAt d.n level base z c ix u) :
    ∃v b, Executes d.n m loopBody s v b ∧ b ≤ k+j+8 ∧ StackAt d.n level base z c ix v ∧ v.output=u.output := by
  obtain ⟨a,pre,ka⟩ := splitChain header head_
  obtain ⟨v,flag,im,out⟩:=normal_flag d w level base m z u c ix data image
  rw [body_code]
  exact ⟨v,_,pre.continue _ (.seq act (.seq flag (.skip _))),by omega,im,out⟩

private lemma unitReg {d : Instance} {w level base : ℕ} {z s : State} {c : List ℕ} {ix : ℤ}
    (D : TraversalData d w z) (im : StackAt d.n level base z c ix s) : s.reg 6=1 :=
  (im.between.control 6 (.inl rfl)).trans D.one

private lemma run_moves (d : Instance) (w level V base : ℕ) (m : ℤ→ℤ) (z : State)
    (_pos : 0<d.n) (data : TraversalData d w z) (below : (z.reg 8).toNat ≤ base)
    (visits : Visits d w level m z V) : Moves d w level base m z V := by
  classical
  constructor
  · intro c q s qn can disabled im
    obtain ⟨a,k,h,kt,atA,top,test,ao⟩:=inspect d w level base m z s c q data im
    obtain ⟨b,l,dec,lt,atB,flag,bo⟩:=decrement_at d w level base q m z a c data below atA top qn
    have enter : a.reg 6 ≤ a.reg 1182 := by rw [unitReg data atA,test,if_pos can]
    have inactive : ¬b.reg 6 ≤ b.reg 1195 := by rw [unitReg data atB,flag];simp [disabled]
    obtain ⟨i,pre,li⟩:=splitChain decrement dec
    have branch : Executes d.n m advance a b (i+(1+(1+1)+1)) :=
      pre.continue _ (.seq (.no inactive (.skip _)) (.skip _))
    obtain ⟨t,j,run,jt,done_,out⟩:=run_normal data h (show Executes d.n m dispatch a b _ from .yes enter branch) atB
    exact ⟨t,j,run,by omega,done_,out.trans (bo.trans ao)⟩
  · intro c q s qn can enabled valid length_ _ im
    obtain ⟨a,k,h,kt,atA,top,test,ao⟩:=inspect d w level base m z s c q data im
    obtain ⟨b,l,dec,lt,atB,flag,bo⟩:=decrement_at d w level base q m z a c data below atA top qn
    have enter : a.reg 6 ≤ a.reg 1182 := by rw [unitReg data atA,test,if_pos can]
    have active : b.reg 6 ≤ b.reg 1195 := by rw [unitReg data atB,flag];simp [enabled]
    have cn : c.length<d.n := by have := can.2;omega
    obtain ⟨u,j,init,jt,atU,input,uo⟩:=push_at d w level base q m z b c data below atB
      ((dec.preserves 265 (by decide)).trans top) qn cn
    obtain ⟨v,x,vis,xt,uv,vo⟩:=visits u (c++[q]) atU.between valid input
    have atV:=after_call atU (by simp;omega) vis uv
    let v':=v.assign 1215 (v.reg 258)
    have ret : Executes d.n m pushReturn v v' 1 := .op rfl
    have fret : Frame v v' := by
      refine ⟨?_,rfl,rfl⟩
      intro r hr;apply ret.preserves
      simp [pushReturn,writesReg,writesOp];unfold layoutReg at hr;omega
    have atV' := unchanged atV fret (by rfl) (by rfl) (by rfl) rfl
    obtain ⟨i,pre,li⟩:=splitChain decrement dec
    obtain ⟨y,pk,jy⟩:=splitChain pushList init
    have child : Executes d.n m descend b v' (y+(1+x+(1+1+1))) := pk.continue _ (.seq vis (.seq ret (.skip _)))
    have path : Executes d.n m advance a v' (i+(1+(1+(y+(1+x+(1+1+1))))+1)) :=
      pre.continue _ (.seq (.yes active child) (.skip _))
    have action : Executes d.n m dispatch a v' (1+(i+(1+(1+(y+(1+x+(1+1+1))))+1))) := .yes enter path
    obtain ⟨t,h',run,ht,done_,out⟩:=run_normal data h action atV'
    refine ⟨t,h',run,by omega,done_,?_⟩
    change t.output=v.output at out
    simpa [uo,bo,ao] using out.trans vo
  · intro c q next s qn cn fresh cap im
    obtain ⟨a,k,h,kt,atA,_,test,ao⟩:=inspect d w level base m z s (c++[q]) next data im
    obtain ⟨b,l,back,lt,atB,bo⟩:=pop_at d w level base q m z a c next data below atA qn cn fresh
    have exit_ : ¬a.reg 6 ≤ a.reg 1182 := by rw [unitReg data atA,test,if_neg cap];decide
    obtain ⟨t,j,run,jt,done_,out⟩:=run_normal data h (show Executes d.n m dispatch a b _ from .no exit_ back) atB
    exact ⟨t,j,run,by omega,done_,out.trans (bo.trans ao)⟩
  · intro ix s cap im
    obtain ⟨a,k,h,kt,atA,_,test,ao⟩:=inspect d w level base m z s [] ix data im
    obtain ⟨b,l,back,lt,flag,one,persistent_,bo⟩:=stop_at d w level base m z a ix data atA
    have exit_ : ¬a.reg 6 ≤ a.reg 1182 := by rw [unitReg data atA,test,if_neg cap];decide
    let t:=b.assign 1166 0
    have halt : Executes d.n m resetFlag b t 2 := by
      apply evalLine_sound
      simp [resetFlag,evalLine,Operation.next,regularNext,State.assign,t,flag,one]
    have keep : Between z t := by
      apply persistent persistent_ (s:=b) (t:=t)
        ⟨by intro j hj;apply halt.preserves;simp [resetFlag,writesReg,writesOp];unfold layoutReg at hj;omega,rfl,rfl⟩
      exact fun _ _=>rfl
    obtain ⟨x,pre,kx⟩:=splitChain header h
    rw [body_code]
    exact ⟨t,_,pre.continue _ (.seq (.no exit_ back) (.seq halt (.skip _))),by omega,
      by simp [t,State.assign,one],keep,bo.trans ao⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal

theorem solution :
∀(d : SingleCircuit.Instance) (w level V base : ℕ) (m : ℤ→ℤ) (z : Logical.State),
    0<d.n → Scene.CutTraversal.TraversalData d w z → (z.reg 8).toNat ≤ base →
    Scene.CutTraversal.Visits d w level m z V → Scene.CutTraversal.Moves d w level base m z V := Scene.CutTraversal.run_moves

#print axioms solution
