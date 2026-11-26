-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.request_child_by_its_boundary
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:48:36.726948+00:00
-- url     : https://prove2.me/submissions/209ca71c-e61c-486d-a980-c5fffff71bfa

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_SeparatorRows_component_rim_bitmap
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_SeparatorKeys_name_key_from_tables
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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open TightLanguage SingleCircuit
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


private def reqSetup : List Program := [.op (.regular (.copy 974 143)),.op (.regular (.copy 237 974)),
 .op (.regular (.copy 153 235)),.op (.regular (.copy 154 237)),.op (.regular (.copy 155 225))]
private def reqOutput : List Program := [.op (.regular (.copy 976 158)),.op (.regular (.copy 238 976)),
 .op (.regular (.set 981 1)),.op (.regular (.set 983 0)),.op (.regular (.copy 218 981)),
 .op (.regular (.copy 219 238)),.op (.regular (.copy 220 983))]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open Scene.CutTraversal TightLanguage SingleCircuit
theorem solution (d : SingleCircuit.Instance) (cursor active points edge table words maxWord : ℕ) (m : ℤ→ℤ)
    (s : Logical.State) (member : ℕ→Bool) (row : SingleCircuit.Assignment) (slot : ℕ→ℕ)
    (one : s.reg 6=1) (zero : s.reg 7=0) (size : s.reg 64=(d.n:ℤ)) (alloc : s.reg 8=(cursor:ℤ))
    (activeAt : s.reg 71=(active:ℤ)) (pointsAt : s.reg 235=(points:ℤ)) (edgeAt : s.reg 75=(edge:ℤ))
    (tableAt : s.reg 225=(table:ℤ)) (wordsAt : s.reg 76=(words:ℤ)) (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ))
    (vertices : ∀p<d.n,s.heap (active+p)=if d.active p then 1 else 0)
    (component : ∀p<d.n,s.heap (points+p)=if member p then 1 else 0)
    (graph : ∀q<d.n,∀p<d.n,s.heap (edge+(q*d.n+p))=if d.edge q p then 1 else 0)
    (below : ∀p<d.n,active+p<cursor ∧ points+p<cursor) (edgeEnd : ∀q<d.n,∀p<d.n,edge+(q*d.n+p)<cursor) :
    let C:=(List.range d.n).filter member
    let B:=TightLanguage.rimOf d C
    (∀p∈B,table+p<cursor ∧ s.heap (table+p)=(slot p:ℤ) ∧ words+slot p<cursor ∧
      s.heap (words+slot p)=(TightLanguage.value row p:ℤ) ∧ TightLanguage.value row p ≤ maxWord) →
    ∃t k, Logical.Executes d.n m (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction src_trial 9)) 1)) 9)) s t k ∧
      k ≤ 700*(d.n+1)^3+600*(d.n+1)*(d.n+maxWord+1)+300+d.n*(165+6*d.n) ∧ t.reg 8=((cursor+d.n:ℕ):ℤ) ∧
      (∀p,p<cursor ∨ cursor+d.n ≤ p → t.heap p=s.heap p) ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
      t.output=s.output++[Instr.need (Naming.name (C,TightLanguage.restricted B row))] := by
  dsimp only;intro labels
  let C:=(List.range d.n).filter member
  let B:=rimOf d C
  let key:=Naming.name (C,restricted B row)
  let a:=s.assign 139 (s.reg 235)
  have start : Logical.Executes d.n m (.op (.regular (.copy 139 235))) s a 1 := .op rfl
  obtain ⟨u,k,rim,bt,br,cur,bits,frame,out,cl⟩:=Scene.SeparatorRows.component_rim_bitmap d.n cursor active points edge m a d.active member d.edge
    (by simpa [a,Logical.State.assign] using one) (by simpa [a,Logical.State.assign] using zero)
    (by simpa [a,Logical.State.assign] using size) (by simpa [a,Logical.State.assign] using alloc)
    (by simpa [a,Logical.State.assign] using activeAt) (by simp [a,Logical.State.assign,pointsAt])
    (by simpa [a,Logical.State.assign] using edgeAt) vertices component graph below edgeEnd
  have preg (j : ℕ) (h : writesReg j src_rim=false) (h' : j≠139) : u.reg j=s.reg j := by
    simpa [a,Logical.State.assign,h'] using rim.preserves j h
  let r:=((((u.assign 974 (cursor:ℤ)).assign 237 (cursor:ℤ)).assign 153 (points:ℤ)).assign 154 (cursor:ℤ)).assign 155 (table:ℤ)
  have up:= (preg 235 (by decide) (by decide)).trans pointsAt
  have uv:= (preg 225 (by decide) (by decide)).trans tableAt
  have setup : Logical.Executes d.n m (chain reqSetup) u r 11 := by
    apply evalLine_sound;simp [reqSetup,chain,evalLine,Operation.next,regularNext,Logical.State.assign,r,br,up,uv]
  have keep (j : ℕ) (h : writesReg j (chain reqSetup)=false) (h' : writesReg j src_rim=false) (no:j≠139) :=
    (setup.preserves j h).trans (preg j h' no)
  have mem (p : ℕ) (hp:p<d.n) : p∈B ↔ d.active p=true ∧ member p=false ∧ ∃q<d.n,member q=true ∧ d.edge q p=true := by
    simp [B,rimOf,TightLanguage.vertices,C,List.any_eq_true,hp,and_assoc,and_left_comm,and_comm]
  have orderB : (List.range d.n).filter (fun j=>decide (j∈B))=B := by
    have existsFilter : ∃f:ℕ→Bool,B=(List.range d.n).filter f := by
      unfold B rimOf TightLanguage.vertices;rw [List.filter_filter];exact ⟨_,rfl⟩
    obtain ⟨f,hf⟩:=existsFilter;rw [hf];apply List.filter_congr;intro i hi;cases e:f i <;> simp [e,hi]
  obtain ⟨v,l,name,nt,encoded,nheap,ncur,nout,ncl⟩:=Scene.SeparatorKeys.name_key_from_tables
    d.n points cursor table words maxWord m r member (fun j=>decide (j∈B)) slot (value row)
    ((keep 6 (by decide) (by decide) (by decide)).trans one) ((keep 64 (by decide) (by decide) (by decide)).trans size)
    (by simp [r,Logical.State.assign]) (by simp [r,Logical.State.assign]) (by simp [r,Logical.State.assign])
    ((keep 76 (by decide) (by decide) (by decide)).trans wordsAt) (by
      intro p hp;change 1 ≤ u.heap (points+p) ↔ _
      rw [frame _ (.inl (below p hp).2)];change 1 ≤ s.heap (points+p) ↔ _;rw [component _ hp];cases member p <;> decide)
    (by intro p hp;change 1 ≤ u.heap (cursor+p) ↔ _;rw [bits p hp];simp only [decide_eq_true_eq,mem p hp];split <;> simp_all)
    (by intro p _ hp;have h:=labels p (of_decide_eq_true hp);change u.heap (table+p)=_;rw [frame _ (.inl h.1)];exact h.2.1)
    (by intro p _ hp;have h:=labels p (of_decide_eq_true hp);change u.heap (words+slot p)=_;rw [frame _ (.inl h.2.2.1)];exact h.2.2.2.1)
    (by intro p _ hp;exact (labels p (of_decide_eq_true hp)).2.2.2.2)
  rw [orderB] at encoded
  change v.reg 158=(key:ℤ) at encoded
  have v1:= (name.preserves 6 (by decide)).trans ((keep 6 (by decide) (by decide) (by decide)).trans one)
  have vs:= (name.preserves 64 (by decide)).trans ((keep 64 (by decide) (by decide) (by decide)).trans size)
  have vct:= (name.preserves 82 (by decide)).trans ((keep 82 (by decide) (by decide) (by decide)).trans count)
  have vo : v.output=s.output := nout.trans out
  have vc : v.closed=false := ncl.trans (cl.trans ready)
  let g:=((((((v.assign 976 (key:ℤ)).assign 238 (key:ℤ)).assign 981 1).assign 983 0).assign 218 1).assign 219 (key:ℤ)).assign 220 0
  have ops : Logical.Executes d.n m (chain reqOutput) v g 15 := by
    apply evalLine_sound;simp [reqOutput,chain,evalLine,Operation.next,regularNext,Logical.State.assign,g,encoded]
  let y : Logical.State := {g.assign 82 (g.reg 82+1) with output:=g.output++[.need key]}
  have recEq : record d.n g=.need key := by simp [record,g,Logical.State.assign]
  have emit : Logical.Executes d.n m (.op .output) g y (200+d.n*(165+6*d.n)) := by
    apply Logical.Executes.op;simp only [Operation.next,recEq]
    simp [Logical.State.bitsOK,Instr.tag,Instr.arg,y,g,Logical.State.assign,v1,vs,vct,vo,vc]
  let t:=y.assign 980 (y.reg 222)
  have last : Logical.Executes d.n m (.op (.regular (.copy 980 222))) y t 1 := .op rfl
  obtain ⟨so,hso,eso⟩:=splitChain reqOutput ops
  obtain ⟨ss,hss,ess⟩:=splitChain reqSetup setup
  have run := Logical.Executes.seq start (.seq rim (hss.continue _ (.seq name (hso.continue _ (.seq emit (.seq last (.skip _)))))))
  refine ⟨t,_,run,by omega,?_,?_,vc,?_,?_⟩
  · have u8 : r.reg 8=u.reg 8:=setup.preserves 8 (by decide)
    simpa [t,y,g,Logical.State.assign] using ncur.trans (u8.trans cur)
  · intro p hp;change v.heap p=_;rw [nheap];exact frame p hp
  · simp [t,y,g,Logical.State.assign,vct,vo]
  · change v.output++[.need key]=_;rw [vo]

#print axioms solution
