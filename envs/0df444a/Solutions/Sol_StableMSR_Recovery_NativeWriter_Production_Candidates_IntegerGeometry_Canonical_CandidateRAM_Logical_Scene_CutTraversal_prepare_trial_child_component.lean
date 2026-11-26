-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.prepare_trial_child_component
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:42:12.87186+00:00
-- url     : https://prove2.me/submissions/275be7e7-f94a-411c-8015-d8466c71ef68

import Definitions.Def_StableMSR_RegionalMenuImage
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 35000
private theorem source_loop {N:ℕ} {input:ℤ → ℤ} (ix last n cap:ℕ) (body:Program) (P:ℕ→State→Prop) (ne:ix≠last)
    (step:∀i < n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1)))
    (i rem:ℕ) (len:i+rem=n) (s:State) (start:P i s) (idx:s.reg ix=(i:ℤ)) (lim:s.reg last=(n:ℤ)-1) :
    ∃t k,Executes N input (.loop ix last (chain [body,.op (.regular (.inc ix))])) s t k ∧ k≤1+rem*(cap+5) ∧ P n t :=by
  induction rem generalizing i s with
  | zero=>
    have eq:i=n:=by omega
    exact ⟨s,1,.stop (by rw [idx,lim];omega),by omega,eq ▸ start⟩
  | succ r ih=>
    have lt:i < n:=by omega
    obtain ⟨u,k,ex,tim,idx',lim',next⟩:=step i lt s start idx lim
    let v:=u.assign ix (u.reg ix+1)
    have vi:v.reg ix=((i+1:ℕ):ℤ):=by simp [v,State.assign,idx',idx]
    have vl:v.reg last=(n:ℤ)-1:=by simp [v,State.assign,Ne.symm ne,lim',lim]
    obtain ⟨t,z,more,tm,out⟩:=ih (i+1) (by omega) v next vi vl
    have full:Executes N input (chain [body,.op (.regular (.inc ix))]) s v (1+k+(1+1+1)):=.seq ex (.seq (.op rfl) (.skip _))
    exact ⟨t,_,.more (by rw [idx,lim];omega) full more,by rw [Nat.succ_mul];omega,out⟩

private def forSetup (ix last len:ℕ) (s:State) := let u:=s.assign ix 0; let v:=u.assign last (u.reg len);v.assign last (v.reg last-1)
private theorem source_for {N:ℕ} {input:ℤ → ℤ} (ix last len n cap:ℕ) (body:Program) (P:ℕ→State→Prop)
    (ne:ix≠last) (dis:len≠ix) (s:State) (size:s.reg len=(n:ℤ))
    (start:P 0 (forSetup ix last len s))
    (step:∀i < n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1))) :
    ∃t k,Executes N input (forCount ix last len body) s t k ∧ k≤9+n*(cap+5) ∧ P n t :=by
  let u:=forSetup ix last len s
  have fi:u.reg ix=0:=by simp [u,forSetup,State.assign,ne]
  have last':u.reg last=(n:ℤ)-1:=by simp [u,forSetup,State.assign,dis,size]
  obtain ⟨t,z,loop,tm,out⟩:=source_loop ix last n cap body P ne step 0 n (by omega) u start fi last'
  refine ⟨t,_,.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq loop (.skip _)))),by omega,out⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
private def writesOp (j:ℕ) : Operation → Bool
  | .regular (.store _ _)|.save _ _ _=>false
  | .regular (.set d _)|.regular (.copy d _)|.regular (.add d _ _)|.regular (.sub d _ _)|
    .regular (.inc d)|.regular (.dec d)|.regular (.load d _)|.multiply d _ _|.divide _ d _ _|
    .fetch d _ _|.shift d _ _=>j==d
  | .alloc d _=>j==d || j==8
  | .output=>j==82
private def writesReg (j:ℕ) : Program → Bool
  | .skip=>false | .op o=>writesOp j o | .seq p q|.cond _ _ p q=>writesReg j p || writesReg j q
  | .loop _ _ p=>writesReg j p
private theorem op_preserves {n input s t k} (o:Operation) (j:ℕ) (frame:writesOp j o=false)
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
private theorem Executes.preserves {n input p s t k} (ex:Executes n input p s t k) (j:ℕ) (off:writesReg j p=false):
    t.reg j=s.reg j:=by
  induction ex with
  | skip|stop=>rfl
  | op h=>exact op_preserves _ _ off h
  | seq _ _ ih jh=>obtain ⟨a,b⟩:=Bool.or_eq_false_iff.mp off;exact (jh b).trans (ih a)
  | yes _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).1
  | no _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).2
  | more _ _ _ ih jh=>exact (jh off).trans (ih off)
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
private lemma outside_for {ix last len r : ℕ} {body : Program}
    (off : writesReg r (forCount ix last len body) = false) :
    r ≠ ix ∧ r ≠ last ∧ writesReg r body = false := by
  simpa [forCount,chain,writesReg,writesOp,and_assoc,and_left_comm,and_comm] using off

private lemma counted {n : ℕ} {m : ℤ → ℤ} (ix last len count cap : ℕ) (body : Program)
    (s : State) (P : ℕ → State → Prop) (ne : ix ≠ last) (dis : len ≠ ix)
    (ixSafe : writesReg ix body = false) (lastSafe : writesReg last body = false)
    (size : s.reg len = (count : ℤ)) (init : P 0 s)
    (ignores : ∀ j u a v, a = ix ∨ a = last → P j u → P j (u.assign a v))
    (step : ∀ i < count, ∀ u, P i u →
      (∀ r, writesReg r (forCount ix last len body) = false → u.reg r = s.reg r) →
      u.reg ix = (i : ℤ) → ∃ t k, Executes n m body u t k ∧ k ≤ cap ∧ P (i+1) t) :
    ∃ t k, Executes n m (forCount ix last len body) s t k ∧
      k ≤ 9+count*(cap+5) ∧ P count t := by
  let Q := fun j u => P j u ∧ ∀ r, writesReg r (forCount ix last len body) = false → u.reg r = s.reg r
  have start : Q 0 (forSetup ix last len s) := by
    refine ⟨ignores _ _ _ _ (.inr rfl) (ignores _ _ _ _ (.inr rfl) (ignores _ _ _ _ (.inl rfl) init)),?_⟩
    intro r off
    obtain ⟨a,b,_⟩ := outside_for off
    simp [forSetup,State.assign,a,b]
  obtain ⟨t,k,run,tm,res,_⟩ := source_for (N:=n) (input:=m) ix last len count cap body Q ne dis s size start (by
    intro i hi u good idx _
    obtain ⟨t,k,ex,tm,next⟩ := step i hi u good.1 good.2 idx
    refine ⟨t,k,ex,tm,ex.preserves _ ixSafe,ex.preserves _ lastSafe,ignores _ _ _ _ (.inl rfl) next,?_⟩
    intro r off
    obtain ⟨a,_,b⟩ := outside_for off
    simpa [State.assign,a] using (ex.preserves r b).trans (good.2 r off))
  exact ⟨t,k,run,tm,res⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
private inductive PrefixRun (N:ℕ) (input:ℤ → ℤ) : List Program → State → State → ℕ → Prop where
  | nil (s:State) : PrefixRun N input [] s s 0
  | cons {p ps s u t a z} : Executes N input p s u a → PrefixRun N input ps u t z →
    PrefixRun N input (p::ps) s t (1+a+z)
private theorem PrefixRun.continue {N input ps s t z} (h:PrefixRun N input ps s t z)
    (q:Program) {u k} (tail:Executes N input q t u k):
    Executes N input (ps.foldr Program.seq q) s u (z+k):=by
  induction h with
  | nil=>simpa using tail
  | cons run _ ih=>
    simpa [Nat.add_assoc] using Executes.seq run (ih tail)
private theorem PrefixRun.finish {N input ps s t z} (h:PrefixRun N input ps s t z):
    Executes N input (chain ps) s t (z+1):=h.continue .skip (.skip t)
private theorem splitChain {N input} (ps:List Program) {s t:State} {k:ℕ} (ex:Executes N input (chain ps) s t k) :
    ∃z,PrefixRun N input ps s t z ∧ k=z+1:=by
  induction ps generalizing s t k with
  | nil=>cases ex;exact ⟨0,.nil _,rfl⟩
  | cons p ps ih=>
    change Executes N input (.seq p (chain ps)) s t k at ex
    cases ex with
    | seq left right=>
      obtain ⟨z,e,h⟩:=ih right
      exact ⟨_,.cons left e,by omega⟩
private def evalLine (n:ℕ) (m:ℤ → ℤ) : Program → State → Option (State×ℕ)
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
private theorem evalLine_sound {n m} (p:Program) (s t:State) (k:ℕ) (ex:evalLine n m p s=some (t,k)):
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


private def removeStep := chain [.op (.fetch 952 223 231),.op (.regular (.copy 951 952)),
  .cond 6 951 (chain [.cond 231 226 (.cond 226 231 (.op (.regular (.set 955 0))) (.op (.regular (.set 955 1))))
    (.op (.regular (.set 955 1))),.op (.regular (.copy 951 955))]) .skip,
  .cond 6 951 (chain [.op (.regular (.set 961 1)),.op (.save 230 231 961)]) .skip]
private def removeSweep := forCount 231 950 64 removeStep
private lemma removeOne (n v i cp dst : ℕ) (m : ℤ→ℤ) (s : State) (flag : Bool)
    (one : s.reg 6=1) (idx : s.reg 231=(i:ℤ)) (vertex : s.reg 226=(v:ℤ)) (comp : s.reg 223=(cp:ℤ))
    (out : s.reg 230=(dst:ℤ)) (bit : s.heap (cp+i)=if flag then 1 else 0) :
    ∃t k,Executes n m removeStep s t k ∧ k ≤ 160 ∧ t.output=s.output ∧ t.closed=s.closed ∧
      ∀p,t.heap p=if p=dst+i ∧ flag=true ∧ i≠v then 1 else s.heap p := by
  let res:=(evalLine n m removeStep s).getD (s,0)
  have a : 0 ≤ (cp:ℤ)+i := by omega
  have b : 0 ≤ (dst:ℤ)+i := by omega
  have ar : ((cp:ℤ)+i).toNat=cp+i := by omega
  have br : ((dst:ℤ)+i).toNat=dst+i := by omega
  refine ⟨res.1,res.2,evalLine_sound _ _ _ _ ?_,?_,?_,?_,?_⟩ <;>
    cases flag <;> simp only [Bool.false_eq_true,if_true,if_false,reduceIte] at bit <;>
    by_cases ge : v ≤ i <;> by_cases le : i ≤ v <;>
    simp [res,removeStep,chain,evalLine,Operation.next,regularNext,State.assign,State.save,one,idx,vertex,comp,out,bit,a,b,ar,br,ge,le,Function.update_apply] <;> try omega
private def deleteImage (n v word scratch dst i : ℕ) (src : ℕ→ℤ) (C : ℕ→Bool) (p : ℕ) : ℤ :=
  if dst ≤ p ∧ p<dst+n then (if p-dst < i ∧ C (p-dst)=true ∧ p-dst≠v then 1 else 0)
  else if p=scratch+v then (word:ℤ) else src p
private lemma nextImage (n v word scratch dst i p : ℕ) (src : ℕ→ℤ) (C : ℕ→Bool) (hi:i<n) :
    (if p=dst+i ∧ C i=true ∧ i≠v then 1 else deleteImage n v word scratch dst i src C p) =
       deleteImage n v word scratch dst (i+1) src C p := by
  unfold deleteImage
  by_cases hit:p=dst+i
  · subst p;simp [hi]
  · by_cases inside:dst ≤ p ∧ p<dst+n
    · have eq : p-dst < i+1 ↔ p-dst < i := by omega
      simp [inside,hit,eq]
    · simp [inside,hit]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open Scene.CutTraversal
theorem solution (n v word cp scratch dst : ℕ) (m : ℤ→ℤ) (s : Logical.State) (inComp : ℕ→Bool)
    (hv : v<n) (separate : cp+n ≤ scratch) (space : scratch+n ≤ dst)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(n:ℤ)) (cursor : s.reg 8=(dst:ℤ))
    (compAt : s.reg 223=(cp:ℤ)) (labelAt : s.reg 225=(scratch:ℤ))
    (vertex : s.reg 226=(v:ℤ)) (slot : s.reg 227=(word:ℤ))
    (bits : ∀q<n,s.heap (cp+q)=if inComp q then 1 else 0) :
    ∃t k, Logical.Executes n m (chain (((listOf src_trial).drop 5).take 4)) s t k ∧ k ≤ 200+300*n ∧
      t.reg 230=(dst:ℤ) ∧ t.reg 8=((dst+n:ℕ):ℤ) ∧ t.output=s.output ∧ t.closed=s.closed ∧
      ∀p,t.heap p=if dst ≤ p ∧ p<dst+n then (if inComp (p-dst) && decide (p-dst≠v) then 1 else 0)
        else if p=scratch+v then (word:ℤ) else s.heap p := by
  let a:=s.save (scratch+v) word
  have store : Logical.Executes n m (.op (.save 225 226 227)) s a 64 := by
    apply Logical.Executes.op;simp [Operation.next,labelAt,vertex,slot,a,show 0 ≤ (scratch:ℤ)+v by omega,show ((scratch:ℤ)+v).toNat=scratch+v by omega]
  let b:=((a.clear dst n).assign 947 dst).assign 8 ((dst+n:ℕ):ℤ)
  have alloc : Logical.Executes n m (.op (.alloc 947 64)) a b (64*(1+n)) := by
    apply Logical.Executes.op;simp [a,b,Operation.next,Logical.State.save,one,zero,cursor,size]
  let g:=b.assign 230 (b.reg 947)
  have copy : Logical.Executes n m (.op (.regular (.copy 230 947))) b g 1 := .op rfl
  have ptr : g.reg 230=(dst:ℤ) := by simp [g,b,Logical.State.assign]
  have rg (j : ℕ) (hj : j≠8 ∧ j≠947 ∧ j≠230) : g.reg j=s.reg j := by
    simp [g,b,a,Logical.State.clear,Logical.State.save,Logical.State.assign,hj]
  let img := fun i=>deleteImage n v word scratch dst i s.heap inComp
  let P := fun i (t:Logical.State)=>t.output=s.output ∧ t.closed=s.closed ∧ ∀p,t.heap p=img i p
  have init : P 0 g := by
    refine ⟨rfl,rfl,?_⟩;intro p;simp [g,b,a,Logical.State.clear,Logical.State.save,Logical.State.assign,
      img,deleteImage,Function.update_apply]
  obtain ⟨t,k,ex,tm,res⟩:=Scene.GeometryTables.counted 231 950 64 n 160 removeStep g P
    (by decide) (by decide) (by decide) (by decide) ((rg 64 (by decide)).trans size) init (by
      intro i u r w hr good;rcases hr with rfl|rfl <;> exact good) (by
      intro i hi u good fr idx
      obtain ⟨o,c,h⟩:=good
      have srcbit : u.heap (cp+i) = if inComp i then 1 else 0 := by
        rw [h];simp only [img,deleteImage,if_neg (show ¬(dst ≤ cp+i ∧ cp+i<dst+n) by omega),
          if_neg (show cp+i≠scratch+v by omega)];exact bits i hi
      obtain ⟨z,l,run,bt,oz,cz,hz⟩:=removeOne n v i cp dst m u (inComp i)
        ((fr 6 (by decide)).trans ((rg 6 (by decide)).trans one)) idx
        ((fr 226 (by decide)).trans ((rg 226 (by decide)).trans vertex)) ((fr 223 (by decide)).trans ((rg 223 (by decide)).trans compAt))
        ((fr 230 (by decide)).trans ptr) srcbit
      refine ⟨z,l,run,bt,oz.trans o,cz.trans c,?_⟩;intro p
      rw [hz,h];exact nextImage n v word scratch dst i p s.heap inComp hi)
  obtain ⟨out,cl,heap⟩:=res
  refine ⟨t,_,.seq store (.seq alloc (.seq copy (.seq ex (.skip _)))),by omega,
    (ex.preserves 230 (by decide)).trans ptr,(ex.preserves 8 (by decide)).trans (by simp [g,b,Logical.State.assign]),out,cl,?_⟩
  intro p;rw [heap];by_cases inside:dst ≤ p ∧ p<dst+n
  · have sm : p-dst<n := by omega
    simp [img,deleteImage,inside,sm]
  · simp [img,deleteImage,inside]

#print axioms solution
