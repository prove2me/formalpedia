-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.scan_distinct_trial_children
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:51:36.93886+00:00
-- url     : https://prove2.me/submissions/3e3b8a06-3e04-41a4-8f78-e658c36a4b2d

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_request_child_by_its_boundary
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_ComponentScan_connected_component_bitmap
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_matrix_and_row_scans
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



open TightLanguage SingleCircuit
private abbrev childEmit := (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction src_trial 9)) 1)) 9))
private def childSetup : List Program := [.op (.regular (.copy 967 138)),.op (.regular (.copy 235 967)),.op (.regular (.copy 144 235))]
private def childCheck : List Program := [.op (.regular (.copy 971 147)),
  .cond 971 232 (.cond 232 971 (.op (.regular (.set 970 1))) (.op (.regular (.set 970 0)))) (.op (.regular (.set 970 0)))]
private def childVisit := chain ([.op (.regular (.copy 132 230)),.op (.regular (.copy 133 232)),src_component] ++
  childSetup ++ [src_first] ++ childCheck ++ [.cond 6 970 childEmit .skip])
private def childStep := chain [.op (.fetch 964 230 232),.cond 6 964 childVisit .skip]
private def eachChild := forCount 232 963 64 childStep
private def region (d : Instance) (mark : ℕ→Bool) (i : ℕ) := pieceAt d ((List.range d.n).filter mark) i
private def requestFor (d : Instance) (row : Assignment) (C : List ℕ) := Instr.need (Naming.name (C,restricted (rimOf d C) row))
private def chooseChild (d : Instance) (mark : ℕ→Bool) (row : Assignment) (i : ℕ) : Option Instr :=
  if mark i && (region d mark i).head?==some i then some (requestFor d row (region d mark i)) else none
private lemma orderedChild (d : Instance) (mark : ℕ→Bool) (seed : ℕ) (hn:0<d.n) :
    (List.range d.n).filter (fun p=>decide (p∈region d mark seed))=region d mark seed := by
  have e : List.range d.n=List.range (d.n-1)++[d.n-1] := by rw [←List.range_succ];congr 1;omega
  have ex : ∃f:ℕ→Bool,region d mark seed=(List.range d.n).filter f := by
    unfold region pieceAt
    rw [e,List.foldl_append,List.foldl_cons,List.foldl_nil,List.filter_filter,←e]
    exact ⟨_,rfl⟩
  obtain ⟨f,h⟩:=ex;rw [h];apply List.filter_congr;intro p hp;cases hm:f p <;> simp [hm,hp]
private structure SceneData (d : Instance) (cap allow active edge table words maxW : ℕ) (s : State) (mark : ℕ→Bool) (row : Assignment) (slot : ℕ→ℕ) : Prop where
  allowed : ∀p<d.n,allow+p<cap ∧ s.heap (allow+p)=if mark p then 1 else 0
  activeBit : ∀p<d.n,active+p<cap ∧ s.heap (active+p)=if d.active p then 1 else 0
  edges : ∀q<d.n,∀p<d.n,edge+(q*d.n+p)<cap ∧ s.heap (edge+(q*d.n+p))=if d.edge q p then 1 else 0
  digits : ∀i∈(List.range d.n).filter mark,∀p∈rimOf d (region d mark i),table+p<cap ∧ s.heap (table+p)=(slot p:ℤ) ∧
    words+slot p<cap ∧ s.heap (words+slot p)=(value row p:ℤ) ∧ value row p ≤ maxW
private lemma SceneData.keep {d cap allow active edge table words maxW s mark row slot} (D : SceneData d cap allow active edge table words maxW s mark row slot)
    {t : State} (heap : ∀p<cap,t.heap p=s.heap p) : SceneData d cap allow active edge table words maxW t mark row slot := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi;obtain ⟨b,h⟩:=D.allowed i hi;exact ⟨b,(heap _ b).trans h⟩
  · intro i hi;obtain ⟨b,h⟩:=D.activeBit i hi;exact ⟨b,(heap _ b).trans h⟩
  · intro i hi j hj;obtain ⟨b,h⟩:=D.edges i hi j hj;exact ⟨b,(heap _ b).trans h⟩
  · intro i hi j hj;obtain ⟨b,h,b',h',hb⟩:=D.digits i hi j hj;exact ⟨b,(heap _ b).trans h,b',(heap _ b').trans h',hb⟩
private lemma childTest (n hd i : ℕ) (m : ℤ→ℤ) (s : State) (head : s.reg 147=(hd:ℤ)) (idx : s.reg 232=(i:ℤ)) :
    ∃t k,Executes n m (chain childCheck) s t k ∧ k≤12 ∧ (1 ≤ t.reg 970 ↔ hd=i) ∧
      t.heap=s.heap ∧ t.closed=s.closed ∧ t.output=s.output := by
  let res:=(evalLine n m (chain childCheck) s).getD (s,0)
  refine ⟨res.1,res.2,evalLine_sound _ _ _ _ ?_,?_,?_,?_,?_,?_⟩ <;>
    by_cases le : hd ≤ i <;> by_cases ge : i ≤ hd <;>
    simp [res,childCheck,chain,evalLine,Operation.next,regularNext,State.assign,idx,head,le,ge] <;> omega

private lemma visitChild (d : Instance) (cap alloc allow active edge table words maxW i : ℕ) (m : ℤ→ℤ) (s : State)
    (mark : ℕ→Bool) (row : Assignment) (slot : ℕ→ℕ) (hi:i<d.n) (enabled : mark i=true)
    (D : SceneData d cap allow active edge table words maxW s mark row slot) (safe : cap≤alloc)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(d.n:ℤ)) (cursor : s.reg 8=(alloc:ℤ))
    (allowAt : s.reg 230=(allow:ℤ)) (activeAt : s.reg 71=(active:ℤ)) (edgeAt : s.reg 75=(edge:ℤ))
    (tableAt : s.reg 225=(table:ℤ)) (wordsAt : s.reg 76=(words:ℤ)) (idx : s.reg 232=(i:ℤ))
    (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ)) :
    ∃t k,Executes d.n m childVisit s t k ∧ k≤1600*(d.n+1)^4+700*(d.n+1)*(d.n+maxW+1)+420 ∧
      s.reg 8≤t.reg 8 ∧ (∀p<cap,t.heap p=s.heap p) ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
      t.output=s.output++(chooseChild d mark row i).toList := by
  let C:=region d mark i
  let a:=(s.assign 132 (s.reg 230)).assign 133 (s.reg 232)
  have ra (j : ℕ) (h : j≠132 ∧ j≠133) : a.reg j=s.reg j := by simp [a,State.assign,h]
  obtain ⟨u,k,comp,bt,base,uc,points,frame,out,cl⟩:=Scene.ComponentScan.connected_component_bitmap d mark alloc allow edge i m a hi enabled
    ((ra 6 (by decide)).trans one) ((ra 7 (by decide)).trans zero) ((ra 64 (by decide)).trans size)
    ((ra 8 (by decide)).trans cursor) (by simp [a,State.assign,idx]) (by simp [a,State.assign,allowAt])
    ((ra 75 (by decide)).trans edgeAt) (fun p hp=>(D.allowed p hp).1.trans_le safe) (fun p hp=>(D.allowed p hp).2)
    (fun q hq p hp=>(D.edges q hq p hp).1.trans_le safe) (fun q hq p hp=>(D.edges q hq p hp).2)
  let b:=((u.assign 967 (alloc:ℤ)).assign 235 (alloc:ℤ)).assign 144 (alloc:ℤ)
  have setup : Executes d.n m (chain childSetup) u b 7 := by
    apply evalLine_sound;simp [childSetup,chain,evalLine,Operation.next,regularNext,State.assign,b,base]
  have rb (j : ℕ) (h₁:writesReg j (chain childSetup)=false) (h₂:writesReg j src_component=false) (h₃:j≠132 ∧ j≠133) :=
    (setup.preserves j h₁).trans ((comp.preserves j h₂).trans (ra j h₃))
  obtain ⟨v,l,fr,tf,head,fh,fo,fc⟩:=Logical.matrix_and_row_scans.2.1 d.n alloc m b
    ((rb 6 (by decide) (by decide) (by decide)).trans one) ((rb 64 (by decide) (by decide) (by decide)).trans size)
    (by simp [b,State.assign])
  have ordered := orderedChild d mark i (by omega)
  have repr : (List.range d.n).filter (fun j=>decide (1 ≤ b.heap (alloc+j)))=C := by
    calc _ = (List.range d.n).filter (fun j=>decide (j∈C)) := by
           apply List.filter_congr;intro p hp;change decide (1 ≤ u.heap (alloc+p))=_
           have eq : u.heap (alloc+p)=(if p∈C then 1 else 0) := points p (List.mem_range.mp hp)
           rw [eq];by_cases member:p∈C <;> simp [member]
         _ = _ := ordered
  rw [repr] at head
  obtain ⟨w,z,ch,tz,test,wh,wc,wo⟩:=childTest d.n (C.headD d.n) i m v head
    ((fr.preserves 232 (by decide)).trans ((rb 232 (by decide) (by decide) (by decide)).trans idx))
  have rw0 (j : ℕ) (h₁:writesReg j (chain childCheck)=false) (h₂:writesReg j src_first=false) :
      w.reg j=b.reg j := (ch.preserves j h₁).trans (fr.preserves j h₂)
  have R (j : ℕ) (h₁:writesReg j (chain childCheck)=false) (h₂:writesReg j src_first=false)
      (h₃:writesReg j (chain childSetup)=false) (h₄:writesReg j src_component=false) (h₅:j≠132 ∧ j≠133) : w.reg j=s.reg j :=
    (rw0 j h₁ h₂).trans (rb j h₃ h₄ h₅)
  have w8 : w.reg 8=((alloc+d.n:ℕ):ℤ) := (rw0 8 (by decide) (by decide)).trans ((setup.preserves 8 (by decide)).trans uc)
  have w1 := (R 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans one
  have whp (p:ℕ) : w.heap p=u.heap p := by rw [wh,fh];rfl
  have old (p:ℕ) (h:p<cap) : w.heap p=s.heap p := (whp p).trans (frame _ (.inl (h.trans_le safe)))
  have closed : w.closed=false := wc.trans (fc.trans (cl.trans ready))
  have output : w.output=s.output := wo.trans (fo.trans out)
  have ct : w.reg 82=(w.output.length:ℤ) := by rw [output];exact (R 82 (by decide) (by decide) (by decide) (by decide) (by decide)).trans count
  have ehead : C.headD d.n=i ↔ C.head?=some i := by
    have f (L : List ℕ) : L.headD d.n=i ↔ L.head?=some i := by
      cases L with
      | nil => simp [show d.n≠i by omega]
      | cons a t => simp
    exact f C
  obtain ⟨cb,prb,bEq⟩:=splitChain childSetup setup
  obtain ⟨cc,prc,cEq⟩:=splitChain childCheck ch
  have enter {t : State} {tailCost : ℕ} (tail : Executes d.n m (.cond 6 970 childEmit .skip) w t tailCost) :
      Executes d.n m childVisit s t (1+1+(1+1+(1+k+(cb+(1+l+(cc+(1+tailCost+1))))))) :=
    .seq (.op (o:=.regular (.copy 132 230)) rfl)
       (.seq (.op (o:=.regular (.copy 133 232)) rfl)
         (.seq comp (prb.continue _ (.seq fr (prc.continue _ (.seq tail (.skip _)))))))
  by_cases yes : C.head?=some i
  · have qi : i∈(List.range d.n).filter mark:=List.mem_filter.mpr ⟨List.mem_range.mpr hi,enabled⟩
    obtain ⟨t,j,req,tm,curT,frameT,clT,cntT,outT⟩:=request_child_by_its_boundary d (alloc+d.n) active alloc edge table words maxW m w
      (fun p=>decide (p∈C)) row slot w1 ((R 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans zero)
      ((R 64 (by decide) (by decide) (by decide) (by decide) (by decide)).trans size) w8
      ((R 71 (by decide) (by decide) (by decide) (by decide) (by decide)).trans activeAt)
      ((rw0 235 (by decide) (by decide)).trans (by simp [b,State.assign]))
      ((R 75 (by decide) (by decide) (by decide) (by decide) (by decide)).trans edgeAt)
      ((R 225 (by decide) (by decide) (by decide) (by decide) (by decide)).trans tableAt)
      ((R 76 (by decide) (by decide) (by decide) (by decide) (by decide)).trans wordsAt) closed ct
      (fun p hp=>(old _ (D.activeBit p hp).1).trans (D.activeBit p hp).2)
      (by intro p hp;rw [whp,points p hp];simp [C,region])
      (fun q hq p hp=>(old _ (D.edges q hq p hp).1).trans (D.edges q hq p hp).2)
      (by intro p hp;have := (D.activeBit p hp).1;omega)
      (by intro q hq p hp;have := (D.edges q hq p hp).1;omega)
      (by intro p hp;rw [ordered] at hp;obtain ⟨h,x,g,y,bound⟩:=D.digits i qi p hp
          exact ⟨by omega,(old _ h).trans x,by omega,(old _ g).trans y,bound⟩)
    have full:=enter (.yes (w1 ▸ test.mpr (ehead.mpr yes)) req)
    refine ⟨t,_,full,?_,by rw [cursor,curT];omega,fun p hp=>(frameT _ (.inl (by omega))).trans (old _ hp),clT,cntT,?_⟩
    · ring_nf at bt tf tm ⊢;omega
    · rw [ordered] at outT;simpa [chooseChild,enabled,show (region d mark i).head?=some i from yes,requestFor,output,C] using outT
  · have full:=enter (.no (by rw [w1];exact fun h=>yes (ehead.mp (test.mp h))) (.skip _))
    refine ⟨w,_,full,?_,by rw [cursor,w8];omega,old,closed,ct,?_⟩
    · ring_nf at bt tf ⊢;omega
    · simpa [chooseChild,enabled,show (region d mark i).head?≠some i from yes] using output

private lemma requestsInOrder (d : Instance) (mark : ℕ→Bool) (row : Assignment) :
    (List.range d.n).filterMap (chooseChild d mark row)=
    (parts d ((List.range d.n).filter mark)).map (requestFor d row) := by
  let f:=fun i=>if (region d mark i).head?==some i then some (region d mark i) else none
  have h (xs : List ℕ) : xs.filterMap (chooseChild d mark row)=((xs.filter mark).filterMap f).map (requestFor d row) := by
    induction xs with
    | nil=>rfl
    | cons x xs ih=>
      cases e:mark x <;> by_cases g:(region d mark x).head?=some x <;> simp [chooseChild,List.filterMap_cons,e,g,ih,f]
  exact h _

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open Scene.CutTraversal TightLanguage SingleCircuit
theorem solution (d : SingleCircuit.Instance) (cursor allowed active edge table words maxWord : ℕ) (m : ℤ→ℤ)
    (s : Logical.State) (enabled : ℕ→Bool) (row : SingleCircuit.Assignment) (slot : ℕ→ℕ)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(d.n:ℤ)) (alloc : s.reg 8=(cursor:ℤ))
    (allowAt : s.reg 230=(allowed:ℤ)) (activeAt : s.reg 71=(active:ℤ)) (edgeAt : s.reg 75=(edge:ℤ))
    (tableAt : s.reg 225=(table:ℤ)) (wordsAt : s.reg 76=(words:ℤ)) (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ))
    (allowBits : ∀p<d.n,allowed+p<cursor ∧ s.heap (allowed+p)=if enabled p then 1 else 0)
    (activeBits : ∀p<d.n,active+p<cursor ∧ s.heap (active+p)=if d.active p then 1 else 0)
    (edges : ∀q<d.n,∀p<d.n,edge+(q*d.n+p)<cursor ∧ s.heap (edge+(q*d.n+p))=if d.edge q p then 1 else 0) :
    let U:=(List.range d.n).filter enabled
    (∀seed∈U,∀p∈TightLanguage.rimOf d (TightLanguage.pieceAt d U seed),table+p<cursor ∧ s.heap (table+p)=(slot p:ℤ) ∧
      words+slot p<cursor ∧ s.heap (words+slot p)=(TightLanguage.value row p:ℤ) ∧ TightLanguage.value row p ≤ maxWord) →
    ∃t k,Logical.Executes d.n m (Scene.BlockRows.instruction src_trial 9) s t k ∧
      k ≤ 9+d.n*(1600*(d.n+1)^4+700*(d.n+1)*(d.n+maxWord+1)+505) ∧
      s.reg 8 ≤ t.reg 8 ∧ (∀p<cursor,t.heap p=s.heap p) ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
      t.output=s.output++(TightLanguage.parts d U).map (fun C=>Instr.need (Naming.name (C,TightLanguage.restricted (TightLanguage.rimOf d C) row))) := by
  dsimp only;intro digits
  have data : SceneData d cursor allowed active edge table words maxWord s enabled row slot :=
    ⟨allowBits,activeBits,edges,digits⟩
  let P:=fun j (u:Logical.State)=>s.reg 8 ≤ u.reg 8 ∧ (∀p<cursor,u.heap p=s.heap p) ∧ u.closed=false ∧
    u.reg 82=(u.output.length:ℤ) ∧ u.output=s.output++(List.range j).filterMap (chooseChild d enabled row)
  obtain ⟨t,k,run,bt,next⟩:=Scene.GeometryTables.counted 232 963 64 d.n
    (1600*(d.n+1)^4+700*(d.n+1)*(d.n+maxWord+1)+500) childStep s P
    (by decide) (by decide) (by decide) (by decide) size (by simp [P,ready,count]) (by
      intro j u a v eq good;rcases eq with rfl|rfl <;> simpa [P,Logical.State.assign] using good) (by
      intro i hi u good keep idx
      obtain ⟨cu,old,cl,ct,out⟩:=good
      have D:=data.keep old
      let a:=u.assign 964 (u.heap (allowed+i))
      have ai (q : ℕ) (ne:q≠964) : a.reg q=u.reg q := by simp [a,Logical.State.assign,ne]
      have r (q : ℕ) (ne:q≠964) (safe:writesReg q eachChild=false) := (ai q ne).trans (keep q safe)
      have at6:=(r 6 (by decide) (by decide)).trans one
      have bp:=(keep 230 (by decide)).trans allowAt
      have fetch : Logical.Executes d.n m (.op (.fetch 964 230 232)) u a 64 := by
        apply Logical.Executes.op
        simp only [Operation.next,bp,idx,←Nat.cast_add,Int.natCast_nonneg,if_true,Int.toNat_natCast];rfl
      have chk : a.reg 964=if enabled i then 1 else 0 := (show a.reg 964=u.heap (allowed+i) from by simp [a,Logical.State.assign]).trans (D.allowed i hi).2
      have curA : a.reg 8=((u.reg 8).toNat:ℤ) := by rw [ai 8 (by decide),Int.toNat_of_nonneg (by rw [alloc] at cu;omega)]
      by_cases yes:enabled i=true
      · obtain ⟨b,j,visit,tm,safe,h,bc,bt,bo⟩:=visitChild d cursor (u.reg 8).toNat allowed active edge table words maxWord i m a enabled row slot hi yes
          (D.keep (fun _ _=>rfl)) (by rw [alloc] at cu;omega) at6
          ((r 7 (by decide) (by decide)).trans zero) ((r 64 (by decide) (by decide)).trans size) curA
          ((r 230 (by decide) (by decide)).trans allowAt) ((r 71 (by decide) (by decide)).trans activeAt)
          ((r 75 (by decide) (by decide)).trans edgeAt) ((r 225 (by decide) (by decide)).trans tableAt)
          ((r 76 (by decide) (by decide)).trans wordsAt) ((ai 232 (by decide)).trans idx) cl ((ai 82 (by decide)).trans ct)
        have whole : Logical.Executes d.n m childStep u b (1+64+(1+(1+j)+1)) := .seq fetch (.seq (.yes (by rw [at6,chk,yes];decide) visit) (.skip _))
        refine ⟨b,_,whole,by omega,cu.trans (by simpa [a,Logical.State.assign] using safe),fun p hp=>(h _ hp).trans (old _ hp),bc,bt,?_⟩
        rw [bo];change u.output++_= _;rw [out];simp [List.range_succ,List.filterMap_append,List.append_assoc,List.filterMap_cons];cases chooseChild d enabled row i <;> rfl
      · have no : enabled i=false := Bool.eq_false_iff.mpr yes
        have whole : Logical.Executes d.n m childStep u a (1+64+(1+(1+1)+1)) := .seq fetch (.seq (.no (by rw [at6,chk,no];decide) (.skip _)) (.skip _))
        refine ⟨a,_,whole,by omega,by simpa [a,Logical.State.assign] using cu,old,cl,(ai 82 (by decide)).trans ct,?_⟩
        change u.output=_;rw [out];simp [List.range_succ,List.filterMap_append,chooseChild,no])
  obtain ⟨c,h,cl,ct,out⟩:=next
  exact ⟨t,k,run,by simpa [Nat.add_assoc] using bt,c,h,cl,ct,by rw [out,requestsInOrder];rfl⟩

#print axioms solution
