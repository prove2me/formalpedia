-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.write_single_separator_level
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T12:31:07.922705+00:00
-- url     : https://prove2.me/submissions/e3d783e8-15d9-4de1-ad94-7996386ee704

import Definitions.Def_StableMSR_CutTraversal
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_run_nonempty_cut_stack
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_write_one_separator
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
      ∃t k,Executes N input body s t k ∧ k ≤ cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1)))
    (i rem:ℕ) (len:i+rem=n) (s:State) (start:P i s) (idx:s.reg ix=(i:ℤ)) (lim:s.reg last=(n:ℤ)-1) :
    ∃t k,Executes N input (.loop ix last (chain [body,.op (.regular (.inc ix))])) s t k ∧ k ≤ 1+rem*(cap+5) ∧ P n t :=by
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
      ∃t k,Executes N input body s t k ∧ k ≤ cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1))) :
    ∃t k,Executes N input (forCount ix last len body) s t k ∧ k ≤ 9+n*(cap+5) ∧ P n t :=by
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


open StableMSR.Recovery.SingleCircuit TightLanguage
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open SeparatorLevels
set_option autoImplicit false
set_option maxRecDepth 35000
set_option maxHeartbeats 6000000

private def beginList : List Program := [
  .op (.alloc 1145 64), .op (.regular (.copy 260 1145)),
  .op (.alloc 1147 64), .op (.regular (.copy 261 1147)),
  .op (.regular (.set 1152 1)), .op (.regular (.add 1150 64 1152)),
  .op (.alloc 1149 1150), .op (.regular (.copy 262 1149)),
  .op (.regular (.set 1153 0)), .op (.regular (.copy 263 1153)),
  .op (.regular (.set 1156 0)), .op (.regular (.set 1159 1)),
  .op (.regular (.sub 1157 64 1159)), .op (.save 262 1156 1157),
  .op (.regular (.copy 240 259)), .op (.regular (.copy 241 260)),
  .op (.regular (.copy 242 261)), .op (.regular (.copy 243 263))]
private def resumeList : List Program := [
  .op (.regular (.copy 1160 258)), .op (.regular (.set 1165 0)), .op (.regular (.copy 264 1165)),
  .cond 6 264 (.op (.regular (.set 1166 0))) (.op (.regular (.set 1166 1)))]
private lemma code : src_all_cuts=chain (beginList++[src_visit]++resumeList++[remainingProgram]) := rfl

private lemma transBetween {a b c : State} (ab : Between a b) (bc : Between b c) : Between a c := by
  exact ⟨fun j hj=>(bc.control j hj).trans (ab.control j hj),ab.cursor.trans bc.cursor,
    fun j hj=>(bc.tables j (by have ha:=ab.cursor;omega)).trans (ab.tables j hj),bc.count,bc.available⟩

private structure Opened (n k b : ℕ) (s : State) : Prop where
  input : CutInput n k [] s
  bitmap : s.reg 260=(b:ℤ)
  vector : s.reg 261=((b+n:ℕ):ℤ)
  stack : s.reg 262=((b+n+n:ℕ):ℤ)
  depth : s.reg 263=0
  cursor : s.reg 8=((b+n+n+(n+1):ℕ):ℤ)
  next : s.heap (b+n+n)=(n:ℤ)-1

private lemma start_program (d : Instance) (w level : ℕ) (m : ℤ→ℤ) (z a : State)
    (data : TraversalData d w z) (between : Between z a) (levelAt : a.reg 259=(level:ℤ)) :
    let b:=(a.reg 8).toNat
    ∃u k, Executes d.n m (chain beginList) a u k ∧ k ≤ 400*(d.n+1) ∧
      Between a u ∧ Opened d.n level b u ∧ (∀p<d.n,u.heap (b+p)=0) ∧ u.output=a.output := by
  let b:=(a.reg 8).toNat
  let n:=d.n
  have nonnegative := data.nonnegative.trans between.cursor
  have atB : a.reg 8=(b:ℤ) := by dsimp [b];omega
  have one := (between.control 6 (.inl rfl)).trans data.one
  have zero := (between.control 7 (.inr (.inl rfl))).trans data.zero
  have size : a.reg 64=(n:ℤ) := (between.control 64 (.inr (.inr (by decide)))).trans data.size
  have raw : ∃u k,evalLine d.n m (chain beginList) a=some (u,k) ∧ k ≤ 400*(n+1) ∧
    Opened n level b u ∧ (∀p<n,u.heap (b+p)=0) ∧
    (∀j<b,u.heap j=a.heap j) ∧ u.output=a.output ∧ u.closed=a.closed := by
    have p₂ : 0 ≤ (b:ℤ)+n := by omega
    have p₃ : 0 ≤ (b:ℤ)+n+n := by omega
    have p₄ : 0 ≤ (n:ℤ)+1 := by omega
    have a₂ : ((b:ℤ)+n).toNat=b+n := by omega
    have a₃ : ((b:ℤ)+n+n).toNat=b+n+n := by omega
    have a₄ : ((n:ℤ)+1).toNat=n+1 := by omega
    simp [beginList,chain,evalLine,Operation.next,regularNext,State.clear,State.assign,State.save,one,zero,size,
      atB,levelAt,Nat.cast_add,p₂,p₃,p₄,a₂,a₃,a₄]
    have isZero (q : ℕ) (hq : q<n) :
        Function.update (fun i : ℕ =>
          if (b : ℤ) + (n : ℤ) + (n : ℤ) ≤ (i : ℤ) ∧ i < b+n+n+(n+1) then (0:ℤ)
          else if (b : ℤ) + (n : ℤ) ≤ (i : ℤ) ∧ i < b+n+n then 0 else if b ≤ i ∧ i < b+n then 0 else a.heap i)
          (b+n+n) ((n:ℤ)-1) (b+q)=0 := by
      rw [Function.update_of_ne (by omega)]
      split_ifs <;> omega
    refine ⟨by omega,?_,isZero,?_⟩
    · refine ⟨⟨?_,?_,b,b+n,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
      all_goals first | exact isZero | (simp [Nat.cast_add] <;> intros <;> omega)
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      split_ifs <;> omega
  obtain ⟨u,k,ev,kt,open_,bits,old,out,cl⟩ := raw
  have run := evalLine_sound _ _ _ _ ev
  refine ⟨u,k,run,kt,⟨?_,by have := open_.cursor;omega,old,?_,cl.trans between.available⟩,open_,bits,out⟩
  · intro j hj
    apply run.preserves
    rcases hj with rfl|rfl|⟨l,r⟩
    · decide
    · decide
    · interval_cases j <;> decide
  · rw [out,←between.count];exact run.preserves 82 (by decide)

private lemma empty_first (vs : List ℕ) (w : ℕ) :
    ∃tail,TightLanguage.cuts vs w=[]::tail := by
  induction vs generalizing w with
  | nil => exact ⟨[],rfl⟩
  | cons v vs ih =>
    cases w with
    | zero => exact ⟨[],rfl⟩
    | succ w =>
      obtain ⟨tail,eq⟩:=ih (w+1)
      exact ⟨tail++(cuts vs w).map (v::·),by simp [TightLanguage.cuts,eq]⟩

private lemma start_and_traverse (stack : ∀(d : SingleCircuit.Instance) (w level V base : ℕ) (m : ℤ→ℤ) (z a : Logical.State),
    0<d.n → Scene.CutTraversal.TraversalData d w z → Scene.SeparatorLevels.Between z a →
    (z.reg 8).toNat ≤ base → Scene.CutTraversal.RootStack d.n level base a → Scene.CutTraversal.Visits d w level m z V →
    ∃t k, Logical.Executes d.n m Scene.CutTraversal.remainingProgram a t k ∧
      k ≤ 1000*(V+1)*(d.n+1)^(min w d.n+2) ∧ Scene.SeparatorLevels.Between z t ∧
      t.output=a.output++((TightLanguage.cuts (TightLanguage.vertices d) (min w d.n)).drop 1).flatMap
        (Scene.CutTraversal.cutTape d level))
    (d : Instance) (w level V : ℕ) (m : ℤ→ℤ) (z a : State) (pos : 0<d.n)
    (data : TraversalData d w z) (between : Between z a) (levelAt : a.reg 259=(level:ℤ))
    (visits : Visits d w level m z V) :
    ∃t k, Executes d.n m src_all_cuts a t k ∧
      k ≤ 1500*(V+1)*(d.n+1)^(min w d.n+2) ∧ Between z t ∧ t.output=a.output++levelTape d w level := by
  let b:=(a.reg 8).toNat
  obtain ⟨u,k,init,kt,au,img,empty,out⟩ := start_program d w level m z a data between levelAt
  obtain ⟨tail,ss⟩ := empty_first (vertices d) (min w d.n)
  obtain ⟨v,l,visit,lt,uv,vo⟩ := visits u [] (transBetween between au) (by simp [ss]) img.input
  have zv := transBetween (transBetween between au) uv
  have one := (zv.control 6 (.inl rfl)).trans data.one
  let y:=(((v.assign 1160 (v.reg 258)).assign 1165 0).assign 264 0).assign 1166 1
  have restart : Executes d.n m (chain resumeList) v y 10 := by
    apply evalLine_sound
    simp [resumeList,chain,evalLine,Operation.next,regularNext,State.assign,y,one]
  have zy : Between z y := by
    refine ⟨?_,zv.cursor,zv.tables,?_,zv.available⟩
    · intro j h
      have small : j ≤ 81 := by rcases h with rfl|rfl|⟨_,h⟩ <;> omega
      simpa [y,State.assign,show j≠1160 by omega,show j≠1165 by omega,show j≠264 by omega,show j≠1166 by omega]
        using zv.control j h
    · simpa [y,State.assign] using zv.count
  have root : RootStack d.n level b y := by
    have limit:=img.cursor
    refine ⟨(restart.preserves 259 (by decide)).trans ((visit.preserves 259 (by decide)).trans
        ((init.preserves 259 (by decide)).trans levelAt)),
      (restart.preserves 260 (by decide)).trans ((visit.preserves 260 (by decide)).trans img.bitmap),
      (restart.preserves 261 (by decide)).trans ((visit.preserves 261 (by decide)).trans img.vector),
      (restart.preserves 262 (by decide)).trans ((visit.preserves 262 (by decide)).trans img.stack),
      (restart.preserves 263 (by decide)).trans ((visit.preserves 263 (by decide)).trans img.depth),
      by simp [y,State.assign],by simp [y,State.assign],?_,?_,?_⟩
    · change _ ≤ v.reg 8
      rw [←limit];exact uv.cursor
    · intro p hp
      exact (uv.tables (b+p) (by rw [limit];simp [b] <;> omega)).trans (empty p hp)
    · exact (uv.tables (b+d.n+d.n) (by rw [limit];simp [b] <;> omega)).trans img.next
  obtain ⟨t,j,rest,jt,zt,ot⟩ := stack d w level V b m z y pos data zy (by dsimp [b];have := between.cursor;omega) root visits
  obtain ⟨a₀,ap,atime⟩:=splitChain beginList init
  obtain ⟨b₀,bp,btime⟩:=splitChain resumeList restart
  rw [code]
  refine ⟨t,_,ap.continue _ (.seq visit (bp.continue _ (.seq rest (.skip _)))),?_,zt,?_⟩
  · let B:=(d.n+1)^(min w d.n+2)
    have b1 : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
    have bn : d.n+1 ≤ B := by
      calc
        d.n+1 = (d.n+1)^1 := by simp
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    change j ≤ 1000*(V+1)*B at jt
    change _ ≤ 1500*(V+1)*B
    have vb : B ≤ (V+1)*B := by nlinarith
    have vv : V+1 ≤ (V+1)*B := by nlinarith
    nlinarith
  · change t.output=y.output++_ at ot
    change t.output=a.output++(cuts (vertices d) (min w d.n)).flatMap (cutTape d level)
    change t.output=v.output++_ at ot
    simpa [ss,vo,out,List.append_assoc] using ot


private lemma from_scene (x : World) (s : Store) (r h w : ℕ) (u v z : State)
    (prep : Prepared x.n r h w u) (geo : Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h u v)
    (menus : Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h v z) :
    TraversalData (integerData x.n x.mem s.imem r h) w z := by
  obtain ⟨one,zero,size,_,_,width,_,_,_,_,_,regs,_,_,_⟩ := prep
  have ctrl (j : ℕ) (hj : j=6 ∨ j=7 ∨ 64 ≤ j ∧ j ≤ 81) : z.reg j=u.reg j := by
    apply (menus.controls j (by rcases hj with h|h|h <;> omega)).trans
    exact geo.controls j (by rcases hj with h|h|h <;> omega)
  have cur:=menus.cursor
  refine ⟨(ctrl _ (.inl rfl)).trans one,(ctrl _ (.inr (.inl rfl))).trans zero,
    (ctrl _ (.inr (.inr (by decide)))).trans size,(ctrl _ (.inr (.inr (by decide)))).trans width,
    by omega,0,?_,?_⟩
  · exact (ctrl _ (.inr (.inr (by decide)))).trans (regs ⟨0,by decide⟩)
  · intro p hp
    change p<x.n at hp
    have le : x.n ≤ cursorAt (offsets x.n (sizes x.n h)) 5 := by simp [cursorAt,offsets] <;> omega
    have le' : x.n ≤ cursorAt (offsets x.n (sizes x.n h)) 11 := by simp [cursorAt,offsets] <;> omega
    refine ⟨by omega,?_⟩
    rw [menus.geometry _ (by omega)]
    have cell := geo.active ⟨p,hp⟩
    have region : Bits.piece x.n x.mem (r/x.n) (r%x.n)=WindowProfiles.piece x (r/x.n) (r%x.n) := rfl
    simpa [integerData,arrange,Bits.normalized,Bits.lookup,hp,cursorAt,region] using cell

private lemma magnitude (n cap c D b : ℕ) (e : ℚ) (low : 2 ≤ n) (capN : n+1 ≤ cap) (ep : 0<e) (e1 : e<1) :
    let E:=parameterEnvelope (e:ℝ)
    let w:=widthBound (e:ℝ)
    let V:=c*cap^D*n^(b*E)
    1500*(V+1)*(n+1)^(min w n+2) ≤ (1500*(c+1))*cap^(D+2)*n^((b+2)*E) := by
  let E:=parameterEnvelope (e:ℝ)
  let w:=widthBound (e:ℝ)
  have er : (0:ℝ)<e := by exact_mod_cast ep
  have er' : (e:ℝ)<1 := by exact_mod_cast e1
  have owner : 1 ≤ ownerBound (e:ℝ) := by
    unfold ownerBound
    apply Nat.le_floor
    rw [le_div_iff₀ er];norm_num;linarith
  have width : w ≤ E := by
    have t:=Nat.mul_le_mul_right (w+1) owner
    dsimp [E,parameterEnvelope];dsimp [w] at t ⊢;omega
  have pow1 : (n+1)^min w n ≤ n^(2*E) := by
    calc
      _ ≤ (n^2)^min w n := Nat.pow_le_pow_left (by nlinarith) _
      _ = n^(2*min w n) := (pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by have:=min_le_left w n;omega)
  have cpos : 0<cap := by omega
  have npos : 0<n := by omega
  have units : 1 ≤ cap^D*n^(b*E) := Nat.mul_pos (Nat.pow_pos cpos) (Nat.pow_pos npos)
  have v : c*cap^D*n^(b*E)+1 ≤ (c+1)*cap^D*n^(b*E) := by
    rw [Nat.add_mul,Nat.add_mul,one_mul];omega
  change 1500*(c*cap^D*n^(b*E)+1)*(n+1)^(min w n+2) ≤ _
  rw [pow_add]
  calc
    _ ≤ 1500*((c+1)*cap^D*n^(b*E))*(n^(2*E)*cap^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ v) (Nat.mul_le_mul pow1 (Nat.pow_le_pow_left capN 2))
    _ = _ := by change _=1500*(c+1)*cap^(D+2)*n^((b+2)*E);rw [show (b+2)*E=b*E+2*E by ring,pow_add cap D 2,pow_add n (b*E) (2*E)];ring

lemma from_cut_contracts (stack : ∀(d : SingleCircuit.Instance) (w level V base : ℕ) (m : ℤ→ℤ) (z a : Logical.State),
    0<d.n → Scene.CutTraversal.TraversalData d w z → Scene.SeparatorLevels.Between z a →
    (z.reg 8).toNat ≤ base → Scene.CutTraversal.RootStack d.n level base a → Scene.CutTraversal.Visits d w level m z V →
    ∃t k, Logical.Executes d.n m Scene.CutTraversal.remainingProgram a t k ∧
      k ≤ 1000*(V+1)*(d.n+1)^(min w d.n+2) ∧ Scene.SeparatorLevels.Between z t ∧
      t.output=a.output++((TightLanguage.cuts (TightLanguage.vertices d) (min w d.n)).drop 1).flatMap
        (Scene.CutTraversal.cutTape d level)) (oneCut :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀level<x.n, let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      Scene.CutTraversal.Visits d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)))) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀ level < x.n, ∀ a : Logical.State,
      Scene.SeparatorLevels.Between z a → a.reg 259=(level:ℤ) →
      let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      ∃t k, Logical.Executes x.n s.imem Logical.src_all_cuts a t k ∧
        k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
        Scene.SeparatorLevels.Between z t ∧
        t.output=a.output++Scene.SeparatorLevels.levelTape d (widthBound (e:ℝ)) level := by
  obtain ⟨c,D,b,each⟩:=oneCut
  refine ⟨1500*(c+1),D+2,b+2,?_⟩
  intro e ep e1 x s low high ready bounded r p rp pp bound key u prep v geo z menus level hl a between atLevel
  let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
  have visit:=each e ep e1 x s low high ready bounded r p rp pp bound key u prep v geo z menus level hl
  obtain ⟨t,k,run,kt,kept,out⟩:=start_and_traverse stack d _ level _ s.imem z a (by change 0<x.n;omega)
    (from_scene x s r _ _ u v z prep geo menus) between atLevel visit
  exact ⟨t,k,run,kt.trans (magnitude x.n x.cap c D b e (by omega) (by dsimp [World.cap];omega) ep e1),kept,out⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal

theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀ level < x.n, ∀ a : Logical.State,
      Scene.SeparatorLevels.Between z a → a.reg 259=(level:ℤ) →
      let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      ∃t k, Logical.Executes x.n s.imem Logical.src_all_cuts a t k ∧
        k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
        Scene.SeparatorLevels.Between z t ∧
        t.output=a.output++Scene.SeparatorLevels.levelTape d (widthBound (e:ℝ)) level := Scene.CutTraversal.from_cut_contracts Scene.CutTraversal.run_nonempty_cut_stack Logical.Root.write_one_separator
