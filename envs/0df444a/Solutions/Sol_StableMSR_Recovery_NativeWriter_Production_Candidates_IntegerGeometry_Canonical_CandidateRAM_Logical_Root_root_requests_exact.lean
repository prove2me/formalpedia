-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.root_requests_exact
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T16:32:45.374302+00:00
-- url     : https://prove2.me/submissions/83a19df4-3bc6-4f94-838e-5e7c4a5d8e4e

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_in_place_component_mask
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_matrix_and_row_scans
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_root_key_without_label_reads
import Definitions.Def_StableMSR_RootComponentRequests
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root
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
def zeroed (s t:State) (k:ℕ) :=
    (∀i,t.heap i=if i<k then 0 else s.heap i) ∧ t.output=s.output ∧ t.closed=s.closed
theorem zeroed_init (s:State) : zeroed s s 0:=by simp [zeroed]
theorem zeroed_assign {s t:State} {k:ℕ} (h:zeroed s t k) (d:ℕ) (v:ℤ):zeroed s (t.assign d v) k:=h
theorem zeroed_expand {s t:State} {k:ℕ} (h:zeroed s t k) (l:ℕ):zeroed s (t.clear k l) (k+l):=by
  refine ⟨?_,h.2⟩
  intro i;change (if k ≤ i ∧ i<k+l then 0 else t.heap i)=_
  rw [h.1];split_ifs <;> omega
theorem op_set {N input} (s:State) (d:ℕ) (v:ℤ):Executes N input (.op (.regular (.set d v))) s (s.assign d v) 1:=
  .op rfl
theorem op_copy {N input} (s:State) (d a:ℕ) (v:ℤ) (eq:s.reg a=v):
    Executes N input (.op (.regular (.copy d a))) s (s.assign d v) 1:=by subst v;exact .op rfl
theorem op_add {N input} (s:State) (d a b:ℕ) (A B:ℕ) (ha:s.reg a=(A:ℤ)) (hb:s.reg b=(B:ℤ)):
    Executes N input (.op (.regular (.add d a b))) s (s.assign d ((A+B:ℕ):ℤ)) 1:=by
  apply Executes.op;simp [Operation.next,regularNext,ha,hb]
theorem op_mul {N input} (s:State) (d a b A B:ℕ) (one:s.reg 6=1) (ha:s.reg a=(A:ℤ)) (hb:s.reg b=(B:ℤ)):
    Executes N input (.op (.multiply d a b)) s (s.assign d ((A*B:ℕ):ℤ)) (8+6*B):=by
  apply Executes.op;simp [Operation.next,one,ha,hb]
theorem op_shift {N input} (s:State) (d a k A:ℕ) (ha:s.reg a=(A:ℤ)):
    Executes N input (.op (.shift d a k)) s (s.assign d ((2^k*A:ℕ):ℤ)) (3+2*k):=by
  apply Executes.op;simp [Operation.next,ha]
theorem op_alloc {N input} (s:State) (d l top L:ℕ) (one:s.reg 6=1) (zero:s.reg 7=0)
    (ht:s.reg 8=(top:ℤ)) (hl:s.reg l=(L:ℤ)) :
    Executes N input (.op (.alloc d l)) s (((s.clear top L).assign d (top:ℤ)).assign 8 ((top+L:ℕ):ℤ)) (64*(1+L)):=by
  apply Executes.op;simp [Operation.next,one,zero,ht,hl]

def powerBody:=chain [.op (.multiply 1240 69 64),.op (.regular (.copy 69 1240))]
def powerLoop:=forCount 268 1239 1237 powerBody
theorem run_power {input:ℤ → ℤ} (N n L:ℕ) (s:State) (one:s.reg 6=1) (base:s.reg 64=(n:ℤ))
    (len:s.reg 1237=(L:ℤ)) (v:s.reg 69=1) :
    ∃t k,Executes N input powerLoop s t k ∧ k ≤ 9+L*(17+6*n) ∧ t.reg 69=((n^L:ℕ):ℤ) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed ∧
    ∀j,j≠69 → j≠268 → j≠1239 → j≠1240 → t.reg j=s.reg j:=by
  let P:=fun i (u:State)=>u.reg 69=((n^i:ℕ):ℤ) ∧ u.heap=s.heap ∧ u.output=s.output ∧ u.closed=s.closed ∧
    ∀j,j≠69 → j≠268 → j≠1239 → j≠1240 → u.reg j=s.reg j
  have start:P 0 (forSetup 268 1239 1237 s):=by
    refine ⟨by simpa [forSetup,State.assign] using v,rfl,rfl,rfl,?_⟩
    intro j _ a b _;simp [forSetup,State.assign,a,b]
  have step (i:ℕ) (_:i<L) (u:State) (good:P i u) (_:u.reg 268=(i:ℤ)) (_:u.reg 1239=(L:ℤ)-1) :
      ∃t k,Executes N input powerBody u t k ∧ k ≤ 12+6*n ∧ t.reg 268=u.reg 268 ∧ t.reg 1239=u.reg 1239 ∧
        P (i+1) (t.assign 268 (t.reg 268+1)):=by
    obtain ⟨before,uh,uo,uc,frame⟩:=good
    let a:=u.assign 1240 (((n^i)*n:ℕ):ℤ)
    let t:=a.assign 69 (((n^i)*n:ℕ):ℤ)
    have x:Executes N input (.op (.multiply 1240 69 64)) u a (8+6*n):=
      op_mul u 1240 69 64 _ _ ((frame 6 (by decide) (by decide) (by decide) (by decide)).trans one)
        before ((frame 64 (by decide) (by decide) (by decide) (by decide)).trans base)
    have y:Executes N input (.op (.regular (.copy 69 1240))) a t 1:=op_copy _ _ _ _ (by simp [a,State.assign])
    exact ⟨t,_,.seq x (.seq y (.skip _)),by omega,rfl,rfl,by simp [t,a,State.assign,pow_succ],
      uh,uo,uc,by intro j p q r g;simpa [t,a,State.assign,p,q,g] using frame j p q r g⟩
  obtain ⟨t,k,run,tm,h⟩:=source_for (N:=N) (input:=input) 268 1239 1237 L (12+6*n) powerBody P
    (by decide) (by decide) s len start step
  exact ⟨t,k,run,by simpa only [show 12+6*n+5=17+6*n by omega] using tm,h⟩
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


namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
theorem op_fetch {n input} (s:State) (d a i base j:ℕ) (ptr:s.reg a=(base:ℤ)) (idx:s.reg i=(j:ℤ)):
    Executes n input (.op (.fetch d a i)) s (s.assign d (s.heap (base+j))) 64:=by
  apply Executes.op
  have pos:0 ≤ (base:ℤ)+j:=by positivity
  have val:((base:ℤ)+j).toNat=base+j:=by omega
  simp [Operation.next,ptr,idx,pos,val]
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root
open SingleCircuit TightLanguage WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3500000
set_option maxRecDepth 32000

def maskPoints (m:ℕ → ℤ) (p n:ℕ) := (List.range n).filter fun j=>decide (1 ≤ m (p+j))
theorem component_order (d:Instance) (i:ℕ) (hi:i<d.n) :
    (List.range d.n).filter (fun j=>decide (j∈TightLanguage.pieceAt d (TightLanguage.vertices d) i))=TightLanguage.pieceAt d (TightLanguage.vertices d) i:=by
  let pass:=fun (seen:List ℕ) (_:ℕ)=>(TightLanguage.vertices d).filter fun u=>seen.contains u || seen.any (fun z=>d.edge z u)
  have last (k:ℕ) : ∃p:ℕ→Bool,(List.range (k+1)).foldl pass [i]=(List.range d.n).filter p:=by
    rw [List.range_succ,List.foldl_append];simp only [List.foldl_cons,List.foldl_nil]
    dsimp only [pass,TightLanguage.vertices];rw [List.filter_filter];exact ⟨_,rfl⟩
  obtain ⟨m,hm⟩:=Nat.exists_eq_succ_of_ne_zero (show d.n≠0 by omega)
  obtain ⟨p,hp⟩:=last m
  have h:TightLanguage.pieceAt d (TightLanguage.vertices d) i=(List.range d.n).filter p:=by
    change (List.range d.n).foldl pass [i]=_
    exact (congrArg (fun t=>(List.range t).foldl pass [i]) (show d.n=m+1 from hm)).trans hp
  rw [h];apply List.filter_congr;intro j hj
  cases hp':p j <;> simp [hp',hj]

theorem component_mask (d:Instance) (m:ℕ → ℤ) (base i:ℕ) (hi:i<d.n)
    (bits:∀j<d.n,m (base+j)=if j∈TightLanguage.pieceAt d (TightLanguage.vertices d) i then 1 else 0):
    maskPoints m base d.n=TightLanguage.pieceAt d (TightLanguage.vertices d) i:=by
  rw [←component_order d i hi]
  change (List.range d.n).filter _=(List.range d.n).filter _
  apply List.filter_congr;intro j hj
  rw [bits j (List.mem_range.mp hj)]
  by_cases h:j∈TightLanguage.pieceAt d (TightLanguage.vertices d) i <;> simp [h]

theorem active_mask (d:Instance) (m:ℕ → ℤ) (p:ℕ)
    (flag:∀j<d.n,1 ≤ m (p+j) ↔ d.active j=true):
    maskPoints m p d.n=TightLanguage.vertices d:=by
  apply List.filter_congr;intro j hj
  have eq:=flag j (List.mem_range.mp hj)
  cases e:d.active j <;> simp_all

theorem all_words (d:Instance): (List.range d.n).flatMap (words d)=requests d:=by
  let choose:=fun i=>let c:=TightLanguage.pieceAt d (TightLanguage.vertices d) i; if c.head?==some i then some c else none
  have go (xs:List ℕ):xs.flatMap (words d)=((xs.filter d.active).filterMap choose).map
      (fun c=>Instr.need (Naming.name (c,[]))):=by
    induction xs with
    | nil=>rfl
    | cons i xs ih=>
      cases ha:d.active i <;> by_cases hc:(TightLanguage.pieceAt d (TightLanguage.vertices d) i).head?=some i <;>
        simp [words,choose,ha,hc,ih,List.filterMap_cons]
  exact go _

theorem head_test (c:List ℕ) (n i:ℕ) (hi:i<n) :
    (c.head?==some i)=decide (c.headD n=i):=by
  cases c with
  | nil=>simp [show n≠i by omega]
  | cons a xs=>by_cases eq:a=i <;> simp [eq]

structure Regs (n a ed z l:ℕ) (s:State):Prop where
  one:s.reg 6=1
  zero:s.reg 7=0
  size:s.reg 64=(n:ℤ)
  active:s.reg 71=(a:ℤ)
  edges:s.reg 75=(ed:ℤ)
  blank:s.reg 270=(z:ℤ)
  labels:s.reg 76=(l:ℤ)
def held (p:Program):Bool:=[6,7,64,71,75,270,76].all (fun j=>!(writesReg j p))
theorem Regs.keep {N input p s t k n a ed z l} (hs:Regs n a ed z l s) (ex:Executes N input p s t k)
    (ok:held p=true):Regs n a ed z l t:=by
  simp [held] at ok;obtain ⟨a',b,c,d,e',f,g⟩:=ok
  exact ⟨(ex.preserves _ a').trans hs.one,(ex.preserves _ b).trans hs.zero,(ex.preserves _ c).trans hs.size,
    (ex.preserves _ d).trans hs.active,(ex.preserves _ e').trans hs.edges,(ex.preserves _ f).trans hs.blank,
    (ex.preserves _ g).trans hs.labels⟩
def coherent (s:State):Prop:=s.reg 82=(s.output.length:ℤ) ∧ s.closed=false

theorem send (n name:ℕ) (input:ℤ → ℤ) (s:State)
    (one:s.reg 6=1) (size:s.reg 64=(n:ℤ)) (tag:s.reg 1313=1) (id:s.reg 158=(name:ℤ)) (ready:coherent s):
    ∃t k,Executes n input (chain sendOps) s t k ∧ k ≤ 220+n*(165+6*n) ∧
      t.heap=s.heap ∧ t.output=s.output++[.need name] ∧ coherent t:=by
  obtain ⟨ord,cl⟩:=ready
  have v:∃t k,evalLine n input (chain sendOps) s=some (t,k) ∧ k ≤ 220+n*(165+6*n) ∧
      t.heap=s.heap ∧ t.output=s.output++[.need name] ∧ coherent t:=by
    simp [coherent,sendOps,chain,evalLine,Operation.next,regularNext,State.assign,record,
      Instr.tag,Instr.arg,State.bitsOK,ord,cl,one,size,tag,id] <;> omega
  obtain ⟨t,k,ex,tm,m,o,c⟩:=v;exact ⟨t,k,evalLine_sound _ _ _ _ ex,tm,m,o,c⟩
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root
open SingleCircuit TightLanguage WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3500000
set_option maxRecDepth 32000

abbrev rootFirst := (Logical.matrix_and_row_scans.2.1)
abbrev rootComponent := @Logical.in_place_component_mask
theorem rootKey (n p b l:ℕ) (input:ℤ → ℤ) (s:State) (one:s.reg 6=1)
    (size:s.reg 64=(n:ℤ)) (pt:s.reg 153=(p:ℤ)) (bd:s.reg 154=(b:ℤ)) (ix:s.reg 155=(b:ℤ))
    (lab:s.reg 76=(l:ℤ)) (mask:∀j<n,¬1 ≤ s.heap (b+j)):
    ∃t k,Executes n input src_name_key s t k ∧ k ≤ 1000*(n+1)^2 ∧
      t.reg 158=(Naming.name (maskPoints s.heap p n,[]):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed:=
  Logical.root_key_without_label_reads n p b b l input s one size pt bd ix lab mask
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root
open SingleCircuit TightLanguage WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3500000
set_option maxRecDepth 32000

theorem announce (n p z l:ℕ) (input:ℤ → ℤ) (s:State) (one:s.reg 6=1)
    (sz:s.reg 64=(n:ℤ)) (pt:s.reg 272=(p:ℤ)) (bd:s.reg 270=(z:ℤ)) (table:s.reg 76=(l:ℤ))
    (empty:∀j<n,¬1 ≤ s.heap (z+j)) (ord:coherent s):
    ∃t k,Executes n input (chain announceOps) s t k ∧ k ≤ 1500*(n+1)^2 ∧ t.heap=s.heap ∧
      t.output=s.output++[.need (Naming.name (maskPoints s.heap p n,[]))] ∧ coherent t:=by
  let u:=(((s.assign 1313 1).assign 153 (p:ℤ)).assign 154 (z:ℤ)).assign 155 (z:ℤ)
  let ps:List Program:=[.op (.regular (.set 1313 1)),.op (.regular (.copy 153 272)),
    .op (.regular (.copy 154 270)),.op (.regular (.copy 155 270))]
  have p0:Executes n input (chain ps) s u 9:=by
    apply evalLine_sound;simp [ps,chain,evalLine,Operation.next,regularNext,State.assign,u,pt,bd]
  obtain ⟨b,pre,bt⟩:=splitChain ps p0
  obtain ⟨v,k,key,tm,name,heap,out,cl⟩:=rootKey n p z l input u one sz rfl rfl rfl table empty
  have ov:coherent v:=⟨by rw [out];exact (key.preserves 82 (by decide)).trans ord.1,cl.trans ord.2⟩
  obtain ⟨t,j,wrote,jt,m,stream,good⟩:=send n _ input v ((key.preserves 6 (by decide)).trans one)
    ((key.preserves 64 (by decide)).trans sz) ((key.preserves 1313 (by decide)).trans (by rfl)) name ov
  have full:Executes n input (chain announceOps) s t _:=pre.continue _ (.seq key wrote)
  refine ⟨t,_,full,?_,m.trans heap,?_,good⟩
  · ring_nf at tm jt ⊢ <;> omega
  · rw [stream,out];rfl

theorem head_decision (n h i:ℕ) (input:ℤ → ℤ) (s:State) (head:s.reg 1309=(h:ℤ)) (idx:s.reg 271=(i:ℤ)):
    ∃k,Executes n input equalHead s (s.assign 1308 (if h=i then 1 else 0)) k ∧ k ≤ 3:=by
  have step:∃k,evalLine n input equalHead s=some (s.assign 1308 (if h=i then 1 else 0),k) ∧ k ≤ 3:=by
    by_cases hi:h ≤ i <;> by_cases ih:i ≤ h <;> by_cases eq:h=i <;>
      simp [equalHead,evalLine,Operation.next,regularNext,head,idx,hi,ih,eq] <;> omega
  obtain ⟨k,ex,le⟩:=step;exact ⟨k,evalLine_sound _ _ _ _ ex,le⟩

theorem select_request (n p z l i h:ℕ) (input:ℤ → ℤ) (s:State) (one:s.reg 6=1)
    (sz:s.reg 64=(n:ℤ)) (pt:s.reg 272=(p:ℤ)) (bd:s.reg 270=(z:ℤ)) (lab:s.reg 76=(l:ℤ))
    (head:s.reg 1309=(h:ℤ)) (idx:s.reg 271=(i:ℤ)) (blank:∀j<n,¬1 ≤ s.heap (z+j)) (ord:coherent s):
    ∃t k,Executes n input (chain [equalHead,announceIf]) s t k ∧ k ≤ 1510*(n+1)^2 ∧ t.heap=s.heap ∧
      t.output=s.output++(if h=i then [.need (Naming.name (maskPoints s.heap p n,[]))] else []) ∧ coherent t:=by
  let u:=s.assign 1308 (if h=i then 1 else 0)
  obtain ⟨k,decision,tm⟩:=head_decision n h i input s head idx
  by_cases eq:h=i
  · obtain ⟨t,j,run,jt,m,o,c⟩:=announce n p z l input u one sz pt bd lab blank ord
    have br:Executes n input announceIf u t (1+j):=.yes (by simp [u,State.assign,one,eq]) run
    exact ⟨t,_,.seq decision (.seq br (.skip _)),by ring_nf at jt ⊢ <;> omega,m,by simpa [eq,u,State.assign] using o,c⟩
  · have br:Executes n input announceIf u u 2:=.no (by simp [u,State.assign,one,eq]) (.skip _)
    exact ⟨u,_,.seq decision (.seq br (.skip _)),by ring_nf <;> omega,rfl,by simp [u,eq,State.assign],ord⟩
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root
open SingleCircuit TightLanguage WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3500000
set_option maxRecDepth 32000

theorem inspect (d:Instance) (p z l i:ℕ) (input:ℤ → ℤ) (s:State) (hi:i<d.n)
    (one:s.reg 6=1) (sz:s.reg 64=(d.n:ℤ)) (pts:s.reg 138=(p:ℤ))
    (bd:s.reg 270=(z:ℤ)) (lab:s.reg 76=(l:ℤ)) (idx:s.reg 271=(i:ℤ))
    (bits:∀j<d.n,s.heap (p+j)=if j∈TightLanguage.pieceAt d (TightLanguage.vertices d) i then 1 else 0)
    (empty:∀j<d.n,¬1 ≤ s.heap (z+j)) (ord:coherent s):
    ∃t k,Executes d.n input (chain inspectOps) s t k ∧ k ≤ 1600*(d.n+1)^2 ∧ t.heap=s.heap ∧
      t.output=s.output++(if (TightLanguage.pieceAt d (TightLanguage.vertices d) i).head?==some i then
        [.need (Naming.name (TightLanguage.pieceAt d (TightLanguage.vertices d) i,[]))] else []) ∧ coherent t:=by
  let ps:List Program:=[.op (.regular (.copy 1305 138)),.op (.regular (.copy 272 1305)),.op (.regular (.copy 144 272))]
  let u:=((s.assign 1305 (p:ℤ)).assign 272 (p:ℤ)).assign 144 (p:ℤ)
  have q:Executes d.n input (chain ps) s u 7:=by
    apply evalLine_sound;simp [ps,chain,evalLine,Operation.next,regularNext,State.assign,u,pts]
  obtain ⟨b,pre,pc⟩:=splitChain ps q
  obtain ⟨v,k,first,ft,value,vm,vo,vc⟩:=rootFirst d.n p input u one sz (by rfl)
  let c:=TightLanguage.pieceAt d (TightLanguage.vertices d) i
  have mask:maskPoints s.heap p d.n=c:=component_mask d s.heap p i hi bits
  have val:v.reg 147=(c.headD d.n:ℕ):=by
    change v.reg 147=((maskPoints s.heap p d.n).headD d.n:ℕ) at value
    simpa only [mask] using value
  let r:=v.assign 1309 (c.headD d.n:ℕ)
  have ret:Executes d.n input (.op (.regular (.copy 1309 147))) v r 1:=op_copy _ _ _ _ val
  have m:r.heap=s.heap:=vm
  have o:r.output=s.output:=vo
  have ready:coherent r:=⟨by rw [o];exact (first.preserves 82 (by decide)).trans ord.1,vc.trans ord.2⟩
  obtain ⟨t,j,run,jt,heap,out,good⟩:=select_request d.n p z l i (c.headD d.n) input r
    ((first.preserves 6 (by decide)).trans one) ((first.preserves 64 (by decide)).trans sz)
    ((first.preserves 272 (by decide)).trans (by rfl)) ((first.preserves 270 (by decide)).trans bd)
    ((first.preserves 76 (by decide)).trans lab) (by rfl) ((first.preserves 271 (by decide)).trans idx)
    (by rw [m];exact empty) ready
  have full:Executes d.n input (chain inspectOps) s t _:=pre.continue _ (.seq first (.seq ret run))
  refine ⟨t,_,full,?_,heap.trans m,?_,good⟩
  · ring_nf at ft jt ⊢ <;> omega
  · rw [out,o,m,mask];change _=s.output++(if c.head?==some i then _ else _)
    rw [head_test c d.n i hi];by_cases eq:c.headD d.n=i <;> simp [eq] <;> rfl
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root
open SingleCircuit TightLanguage WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3500000
set_option maxRecDepth 32000

theorem active_step (d:Instance) (a ed z l cur i:ℕ) (input:ℤ → ℤ) (s:State)
    (regs:Regs d.n a ed z l s) (cursor:s.reg 8=(cur:ℤ)) (idx:s.reg 271=(i:ℤ))
    (aa:a+d.n ≤ z) (ee:ed+d.n*d.n ≤ z) (zz:z+d.n ≤ cur) (hi:i<d.n) (yes:d.active i=true)
    (active:∀j<d.n,1 ≤ s.heap (a+j) ↔ d.active j=true)
    (graph:∀j<d.n,∀v<d.n,1 ≤ s.heap (ed+(j*d.n+v)) ↔ d.edge j v=true)
    (empty:∀j<d.n,¬1 ≤ s.heap (z+j)) (ord:coherent s):
    ∃t k,Executes d.n input (chain activeOps) s t k ∧ k ≤ 2500*(d.n+1)^4 ∧
      t.reg 8=((cur+d.n:ℕ):ℤ) ∧ (∀q<cur,t.heap q=s.heap q) ∧
      t.output=s.output++words d i ∧ coherent t:=by
  let ps:List Program:=[.op (.regular (.copy 132 71)),.op (.regular (.copy 133 271))]
  let u:=(s.assign 132 (a:ℤ)).assign 133 (i:ℤ)
  have ex:Executes d.n input (chain ps) s u 5:=by
    apply evalLine_sound;simp [ps,chain,evalLine,Operation.next,regularNext,State.assign,u,regs.active,idx]
  obtain ⟨b,pre,pc⟩:=splitChain ps ex
  obtain ⟨v,k,comp,tm,ptr,free,bits,frame,out,cl⟩:=rootComponent d a ed cur i input u regs.one regs.zero
    regs.size cursor (by rfl) (by rfl) regs.edges (by omega) (by omega) hi ((active i hi).mpr yes) graph
  have mask:maskPoints s.heap a d.n=TightLanguage.vertices d:=active_mask d s.heap a active
  have correct (j:ℕ) (hj:j<d.n):v.heap (cur+j)=if j∈TightLanguage.pieceAt d (TightLanguage.vertices d) i then 1 else 0:=by
    have eq:=bits j hj
    change v.heap (cur+j)=(if j∈TightLanguage.pieceAt d (maskPoints s.heap a d.n) i then 1 else 0) at eq
    rw [mask] at eq;exact eq
  have newBlank (j:ℕ) (hj:j<d.n):¬1 ≤ v.heap (z+j):=by rw [frame _ (Or.inl (by omega))];exact empty j hj
  have good:coherent v:=⟨by rw [out];exact (comp.preserves 82 (by decide)).trans ord.1,cl.trans ord.2⟩
  obtain ⟨t,j,check,jt,m,o,f⟩:=inspect d cur z l i input v hi ((comp.preserves 6 (by decide)).trans regs.one)
    ((comp.preserves 64 (by decide)).trans regs.size) ptr ((comp.preserves 270 (by decide)).trans regs.blank)
    ((comp.preserves 76 (by decide)).trans regs.labels) ((comp.preserves 271 (by decide)).trans idx) correct newBlank good
  have full:Executes d.n input (chain activeOps) s t _:=pre.continue _ (.seq comp check)
  refine ⟨t,_,full,?_,(check.preserves 8 (by decide)).trans free,?_,?_,f⟩
  · ring_nf at tm jt ⊢ <;> omega
  · intro q hq;rw [m,frame _ (Or.inl hq)];rfl
  · rw [o,out];simp [words,yes,u,State.assign]

theorem step (d:Instance) (a ed z l cur i:ℕ) (input:ℤ → ℤ) (s:State)
    (regs:Regs d.n a ed z l s) (cursor:s.reg 8=(cur:ℤ)) (idx:s.reg 271=(i:ℤ))
    (aa:a+d.n ≤ z) (ee:ed+d.n*d.n ≤ z) (zz:z+d.n ≤ cur) (hi:i<d.n)
    (active:∀j<d.n,1 ≤ s.heap (a+j) ↔ d.active j=true)
    (graph:∀j<d.n,∀v<d.n,1 ≤ s.heap (ed+(j*d.n+v)) ↔ d.edge j v=true)
    (empty:∀j<d.n,¬1 ≤ s.heap (z+j)) (ord:coherent s):
    ∃t k cur',Executes d.n input stepCode s t k ∧ k ≤ 2600*(d.n+1)^4 ∧ cur ≤ cur' ∧
      t.reg 8=(cur':ℤ) ∧ (∀q<cur,t.heap q=s.heap q) ∧ t.output=s.output++words d i ∧ coherent t:=by
  let u:=s.assign 1302 (s.heap (a+i))
  have x:Executes d.n input (.op (.fetch 1302 71 271)) s u 64:=op_fetch s _ _ _ a i regs.active idx
  let guard:=Program.cond 6 1302 (chain activeOps) .skip
  by_cases yes:d.active i=true
  · obtain ⟨t,k,run,tm,ptr,fr,out,cl⟩:=active_step d a ed z l cur i input u (regs.keep x (by decide))
      cursor idx aa ee zz hi yes active graph empty ord
    have br:Executes d.n input guard u t (1+k):=.yes (by change s.reg 6 ≤ s.heap (a+i);rw [regs.one];exact (active i hi).mpr yes) run
    exact ⟨t,_,cur+d.n,.seq x (.seq br (.skip _)),by ring_nf at tm ⊢ <;> omega,by omega,ptr,fr,out,cl⟩
  · have br:Executes d.n input guard u u 2:=.no (by change ¬s.reg 6 ≤ s.heap (a+i);rw [regs.one];exact fun h=>yes ((active i hi).mp h)) (.skip _)
    exact ⟨u,_,cur,.seq x (.seq br (.skip _)),by ring_nf <;> omega,by omega,cursor,fun _ _=>rfl,
      by simp [u,State.assign,words,yes],ord⟩
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root
open SingleCircuit TightLanguage WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3500000
set_option maxRecDepth 32000

theorem square_address {n j v:ℕ} (hj:j<n) (hv:v<n):j*n+v<n*n:=calc
  _ < j*n+n:=Nat.add_lt_add_left hv _
  _ = (j+1)*n:=by ring
  _ ≤ _:=Nat.mul_le_mul_right _ hj

theorem complete (d:Instance) (input:ℤ → ℤ) (s:State) (ok:inputs d s):
    ∃t k,Executes d.n input (chain suffixOps) s t k ∧ k ≤ 10000*(d.n+1)^5 ∧
      t.output=s.output++requests d ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ):=by
  obtain ⟨a,ed,l,z,one,zero,sz,cursor,aaReg,edReg,lab,aa,ee,active,graph,ord,open'⟩:=ok
  let n:=d.n
  let v:=((s.clear z n).assign 1298 (z:ℤ)).assign 8 ((z+n:ℕ):ℤ)
  let u:=v.assign 270 (z:ℤ)
  have al:Executes n input (.op (.alloc 1298 64)) s v (64*(1+n)):=op_alloc s _ _ _ _ one zero cursor sz
  have cp:Executes n input (.op (.regular (.copy 270 1298))) v u 1:=op_copy _ _ _ _ (by rfl)
  have orig(q:ℕ)(hq:q<z):u.heap q=s.heap q:=by
    change (if z ≤ q ∧ q<z+n then 0 else s.heap q)=s.heap q;rw [if_neg (by omega)]
  have blank(j:ℕ)(hj:j<n):¬1 ≤ u.heap (z+j):=by
    change ¬1 ≤ (if z ≤ z+j ∧ z+j<z+n then 0 else s.heap (z+j));rw [if_pos (by omega)];decide
  let P:=fun i (w:State)=>Regs n a ed z l w ∧ coherent w ∧ (∃cur:ℕ,z+n ≤ cur ∧ w.reg 8=(cur:ℤ)) ∧
    (∀q<z+n,w.heap q=u.heap q) ∧ w.output=s.output++(List.range i).flatMap (words d)
  have base:P 0 (forSetup 271 1301 64 u):=by
    exact ⟨⟨one,zero,sz,aaReg,edReg,rfl,lab⟩,⟨ord,open'⟩,⟨z+n,le_rfl,rfl⟩,fun _ _=>rfl,by simp [forSetup,u,v,State.assign,State.clear]⟩
  have adv (i:ℕ) (hi:i<n) (w:State) (valid:P i w) (idx:w.reg 271=(i:ℤ)) (_:w.reg 1301=(n:ℤ)-1):
      ∃t k,Executes n input stepCode w t k ∧ k ≤ 2600*(n+1)^4 ∧ t.reg 271=w.reg 271 ∧
        t.reg 1301=w.reg 1301 ∧ P (i+1) (t.assign 271 (t.reg 271+1)):=by
    obtain ⟨r,oc,⟨cur,space,free⟩,mem,stream⟩:=valid
    have a0(j:ℕ)(hj:j<n):1 ≤ w.heap (a+j) ↔ d.active j=true:=by
      have b:a+j<z:=by change a+n ≤ z at aa;omega
      rw [mem _ (by omega),orig _ b];exact active j hj
    have e0(j:ℕ)(hj:j<n)(v:ℕ)(hv:v<n):1 ≤ w.heap (ed+(j*n+v)) ↔ d.edge j v=true:=by
      have bb:=square_address hj hv
      have b:ed+(j*n+v)<z:=by change ed+n*n ≤ z at ee;omega
      rw [mem _ (by omega),orig _ b];exact graph j hj v hv
    have z0(j:ℕ)(hj:j<n):¬1 ≤ w.heap (z+j):=by rw [mem _ (by omega)];exact blank j hj
    obtain ⟨t,k,cur',run,tm,grow,free',fr,out,cl⟩:=step d a ed z l cur i input w r free idx aa ee space hi a0 e0 z0 oc
    have r':=r.keep run (by decide)
    refine ⟨t,k,run,tm,run.preserves _ (by decide),run.preserves _ (by decide),
      ⟨r'.one,r'.zero,r'.size,r'.active,r'.edges,r'.blank,r'.labels⟩,cl,⟨cur',space.trans grow,free'⟩,?_,?_⟩
    · intro q h;exact (fr q (lt_of_lt_of_le h space)).trans (mem q h)
    · change t.output=_
      simp only [out,stream,List.range_succ,List.flatMap_append,List.flatMap_singleton,List.append_assoc]
  obtain ⟨t,k,scan,tm,r,ok',hcur,hmem,stream⟩:=source_for (N:=n) (input:=input) 271 1301 64 n
    (2600*(n+1)^4) stepCode P (by decide) (by decide) u sz base adv
  have full:Executes n input (chain suffixOps) s t _:=.seq al (.seq cp (.seq scan (.skip _)))
  refine ⟨t,_,full,?_,?_,ok'.2,ok'.1⟩
  · change _ ≤ 10000*(n+1)^5;ring_nf at tm ⊢ <;> omega
  · rw [←all_words];exact stream
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root

set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root
theorem solution (d:Instance) (input:ℤ → ℤ) (s:Logical.State) (ok:Root.inputs d s) :
    ∃t k,Logical.Executes d.n input (Logical.chain Root.suffixOps) s t k ∧ k ≤ 10000*(d.n+1)^5 ∧
      t.output=s.output++Root.requests d ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) := Root.complete d input s ok
