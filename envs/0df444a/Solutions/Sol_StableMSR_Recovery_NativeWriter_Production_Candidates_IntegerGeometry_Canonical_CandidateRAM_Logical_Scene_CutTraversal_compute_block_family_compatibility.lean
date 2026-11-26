-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.compute_block_family_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:19:37.253517+00:00
-- url     : https://prove2.me/submissions/510b131c-f5ba-442d-b2ec-d52b5c912ff5

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_check_selected_block_pair
import Definitions.Def_StableMSR_VertexBlockRows
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


private def leftGuard : List Program := [.op (.regular (.add 799 207 210)),.op (.fetch 797 77 799),.op (.regular (.copy 796 797)),
  .cond 6 796 (chain [.op (.regular (.add 804 207 210)),.op (.fetch 802 79 804),.op (.regular (.copy 796 802))]) .skip]
private def rightGuard : List Program := [.op (.regular (.add 819 208 212)),.op (.fetch 817 77 819),.op (.regular (.copy 816 817)),
  .cond 6 816 (chain [.op (.regular (.add 824 208 212)),.op (.fetch 822 79 824),.op (.regular (.copy 816 822))]) .skip]
private lemma leftGuardRun (n base i rep touch : ℕ) (m : ℤ→ℤ) (s : State) (one : s.reg 6=1)
    (pos : s.reg 207=(base:ℤ)) (idx : s.reg 210=(i:ℤ)) (repAt : s.reg 77=(rep:ℤ)) (touchAt : s.reg 79=(touch:ℤ)) :
    ∃t k, Executes n m (chain leftGuard) s t k ∧ k≤160 ∧
      (1 ≤ t.reg 796 ↔ 1 ≤ s.heap (rep+(base+i)) ∧ 1 ≤ s.heap (touch+(base+i))) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let res := (evalLine n m (chain leftGuard) s).getD (s,0)
  have repN : 0≤(rep:ℤ)+(base+i) := by omega
  have touchN : 0≤(touch:ℤ)+(base+i) := by omega
  have repP : ((rep:ℤ)+(base+i)).toNat=rep+(base+i) := by omega
  have touchP : ((touch:ℤ)+(base+i)).toNat=touch+(base+i) := by omega
  refine ⟨res.1,res.2,evalLine_sound _ _ _ _ ?_,?_,?_,?_,?_,?_⟩ <;>
    by_cases active : 1 ≤ s.heap (rep+(base+i)) <;>
    simp [res,leftGuard,chain,evalLine,Operation.next,regularNext,State.assign,one,pos,idx,repAt,touchAt,
      repN,touchN,repP,touchP,active]
private lemma rightGuardRun (n base i rep touch : ℕ) (m : ℤ→ℤ) (s : State) (one : s.reg 6=1)
    (pos : s.reg 208=(base:ℤ)) (idx : s.reg 212=(i:ℤ)) (repAt : s.reg 77=(rep:ℤ)) (touchAt : s.reg 79=(touch:ℤ)) :
    ∃t k, Executes n m (chain rightGuard) s t k ∧ k≤160 ∧
      (1 ≤ t.reg 816 ↔ 1 ≤ s.heap (rep+(base+i)) ∧ 1 ≤ s.heap (touch+(base+i))) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let res := (evalLine n m (chain rightGuard) s).getD (s,0)
  have repN : 0≤(rep:ℤ)+(base+i) := by omega
  have touchN : 0≤(touch:ℤ)+(base+i) := by omega
  have repP : ((rep:ℤ)+(base+i)).toNat=rep+(base+i) := by omega
  have touchP : ((touch:ℤ)+(base+i)).toNat=touch+(base+i) := by omega
  refine ⟨res.1,res.2,evalLine_sound _ _ _ _ ?_,?_,?_,?_,?_,?_⟩ <;>
    by_cases active : 1 ≤ s.heap (rep+(base+i)) <;>
    simp [res,rightGuard,chain,evalLine,Operation.next,regularNext,State.assign,one,pos,idx,repAt,touchAt,
      repN,touchN,repP,touchP,active]

private abbrev selected := (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction src_fits 10)) 4)) 4)) 4))
private def rightBody := chain (rightGuard ++ [.cond 6 816 selected .skip])
private def leftSetup : List Program := [.op (.regular (.add 810 207 210)),.op (.multiply 809 810 64),
  .op (.regular (.add 807 80 809)),.op (.regular (.copy 211 807))]
private def rightLoop := forCount 212 815 64 rightBody
private def rightProgram := chain (leftSetup ++ [rightLoop])
private def leftBody := chain (leftGuard ++ [.cond 6 796 rightProgram .skip])
private def leftLoop := forCount 210 795 64 leftBody
private abbrev pass {n : ℕ} (C D : Cluster n) := decide (Disjoint C D ∨ C=D)
private structure RowData (n rep touch matrix row : ℕ) (s : State) (E : ℕ→Bool) (A : ℕ→Cluster n) : Prop where
  enabled : ∀i<n,(1 ≤ s.heap (rep+(row+i)) ∧ 1 ≤ s.heap (touch+(row+i))) ↔ E i=true
  bitmap : ∀i<n,E i=true → ∀p:Fin n,s.heap (matrix+((row+i)*n+p.val))=if p∈A i then 1 else 0
private theorem RowData.keep {n rep touch matrix row s E A} (D : RowData n rep touch matrix row s E A)
    {t : State} (heap : t.heap=s.heap) : RowData n rep touch matrix row t E A :=
  ⟨by simpa only [heap] using D.enabled,by simpa only [heap] using D.bitmap⟩

private lemma innerStep (n L R j rep touch mat : ℕ) (m : ℤ→ℤ) (s : State) (C : Cluster n) (B : ℕ→Cluster n) (F : ℕ→Bool)
    (hj : j<n) (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (left : s.reg 211=(L:ℤ))
    (base : s.reg 208=(R:ℤ)) (idx : s.reg 212=(j:ℤ)) (repAt : s.reg 77=(rep:ℤ))
    (touchAt : s.reg 79=(touch:ℤ)) (matAt : s.reg 80=(mat:ℤ)) (D : RowData n rep touch mat R s F B)
    (bitmap : ∀p : Fin n,s.heap (L+p.val)=if p∈C then 1 else 0) :
    ∃t k,Executes n m rightBody s t k ∧ k≤270+340*n ∧
      t.reg 209=(if !F j || pass C (B j) then s.reg 209 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  obtain ⟨a,k,guard,gm,ag,h,o,c⟩:=rightGuardRun n R j rep touch m s one base idx repAt touchAt
  obtain ⟨z,pre,zk⟩:=splitChain rightGuard guard
  have test := ag.trans (D.enabled j hj)
  have a1: a.reg 6=1 := (guard.preserves 6 (by decide)).trans one
  have a209 := guard.preserves 209 (by decide)
  by_cases en : F j=true
  · obtain ⟨v,l,run,tm,flag,h',o',c'⟩:=check_selected_block_pair n R j L mat m a C (B j) a1
      ((guard.preserves 64 (by decide)).trans size) ((guard.preserves 211 (by decide)).trans left)
      ((guard.preserves 208 (by decide)).trans base) ((guard.preserves 212 (by decide)).trans idx)
      ((guard.preserves 80 (by decide)).trans matAt) (by simpa only [h] using bitmap) (by simpa only [h] using D.bitmap j hj en)
    exact ⟨v,_,pre.continue _ (.seq (.yes (a1 ▸ test.mpr en) run) (.skip _)),by omega,
      by simpa [en,pass,a209] using flag,h'.trans h,o'.trans o,c'.trans c⟩
  · exact ⟨a,_,pre.continue _ (.seq (.no (by rw [a1];exact fun h=>en (test.mp h)) (.skip _)) (.skip _)),
      by omega,by simpa [en] using a209,h,o,c⟩

private lemma innerLoop (n L R rep touch mat : ℕ) (m : ℤ→ℤ) (s : State) (C : Cluster n) (B : ℕ→Cluster n) (F : ℕ→Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (left : s.reg 211=(L:ℤ))
    (base : s.reg 208=(R:ℤ)) (repAt : s.reg 77=(rep:ℤ)) (touchAt : s.reg 79=(touch:ℤ))
    (matAt : s.reg 80=(mat:ℤ)) (D : RowData n rep touch mat R s F B)
    (bitmap : ∀p : Fin n,s.heap (L+p.val)=if p∈C then 1 else 0) :
    ∃t k,Executes n m rightLoop s t k ∧ k≤9+n*(275+340*n) ∧
      t.reg 209=(if (List.range n).all (fun j=> !F j || pass C (B j)) then s.reg 209 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let ok := fun j => !F j || pass C (B j)
  let P := fun i (t:State) => t.reg 209=(if (List.range i).all ok then s.reg 209 else 0) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed
  obtain ⟨t,k,run,tm,res⟩:=Scene.GeometryTables.counted 212 815 64 n (270+340*n) rightBody s P
    (by decide) (by decide) (by decide) (by decide) size (by simp [P]) (by
      intro i u j v which good;rcases which with rfl|rfl <;> simpa [P,State.assign] using good) (by
      intro j hj u good fr idx
      obtain ⟨acc,h,o,c⟩:=good
      obtain ⟨v,l,ex,tm,flag,h',o',c'⟩:=innerStep n L R j rep touch mat m u C B F hj ((fr 6 (by decide)).trans one)
        ((fr 64 (by decide)).trans size) ((fr 211 (by decide)).trans left) ((fr 208 (by decide)).trans base)
        idx ((fr 77 (by decide)).trans repAt) ((fr 79 (by decide)).trans touchAt) ((fr 80 (by decide)).trans matAt)
        (D.keep h) (by simpa only [h] using bitmap)
      refine ⟨v,l,ex,tm,?_,h'.trans h,o'.trans o,c'.trans c⟩
      change v.reg 209=(if (List.range (j+1)).all ok then s.reg 209 else 0)
      change v.reg 209=(if ok j then u.reg 209 else 0) at flag
      rw [flag,acc,List.range_succ,List.all_append]
      cases (List.range j).all ok <;> cases hbit : ok j <;> simp [hbit])
  exact ⟨t,k,run,by ring_nf at tm ⊢;exact tm,res⟩

private lemma outerStep (n L R i rep touch mat : ℕ) (m : ℤ→ℤ) (s : State) (A B : ℕ→Cluster n) (E F : ℕ→Bool)
    (hi : i<n) (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (left : s.reg 207=(L:ℤ))
    (base : s.reg 208=(R:ℤ)) (idx : s.reg 210=(i:ℤ)) (repAt : s.reg 77=(rep:ℤ))
    (touchAt : s.reg 79=(touch:ℤ)) (matAt : s.reg 80=(mat:ℤ)) (DL : RowData n rep touch mat L s E A)
    (DR : RowData n rep touch mat R s F B) :
    ∃t k,Executes n m leftBody s t k ∧ k≤200+6*n+n*(275+340*n) ∧
      t.reg 209=(if !E i || (List.range n).all (fun j=> !F j || pass (A i) (B j)) then s.reg 209 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  obtain ⟨a,k,guard,gm,ag,h,o,c⟩:=leftGuardRun n L i rep touch m s one left idx repAt touchAt
  obtain ⟨z,pre,zk⟩:=splitChain leftGuard guard
  have test := ag.trans (DL.enabled i hi)
  have a1:= (guard.preserves 6 (by decide)).trans one
  have a209 := guard.preserves 209 (by decide)
  by_cases en : E i=true
  · let ptr := mat+((L+i)*n)
    let g := (((a.assign 810 ((L+i:ℕ):ℤ)).assign 809 (((L+i)*n:ℕ):ℤ)).assign 807 (ptr:ℤ)).assign 211 (ptr:ℤ)
    have a64 := (guard.preserves 64 (by decide)).trans size
    have a207:= (guard.preserves 207 (by decide)).trans left
    have a210:= (guard.preserves 210 (by decide)).trans idx
    have a80 := (guard.preserves 80 (by decide)).trans matAt
    have head : Executes n m (chain leftSetup) a g (16+6*n) := by
      apply evalLine_sound
      simp [leftSetup,chain,evalLine,Operation.next,regularNext,g,ptr,State.assign,a1,a64,a207,a210,a80,show 0≤(L:ℤ)+i by omega]
      all_goals omega
    have reg (j : ℕ) (off : writesReg j (chain leftSetup)=false) (off' : writesReg j (chain leftGuard)=false) :
        g.reg j=s.reg j := (head.preserves j off).trans (guard.preserves j off')
    have gh : g.heap=s.heap := h
    obtain ⟨v,l,run,tm,flag,h',o',c'⟩:=innerLoop n ptr R rep touch mat m g (A i) B F ((reg 6 (by decide) (by decide)).trans one)
      ((reg 64 (by decide) (by decide)).trans size) (by simp [g,State.assign]) ((reg 208 (by decide) (by decide)).trans base)
      ((reg 77 (by decide) (by decide)).trans repAt) ((reg 79 (by decide) (by decide)).trans touchAt)
      ((reg 80 (by decide) (by decide)).trans matAt) (DR.keep gh) (by simpa only [gh,ptr,Nat.add_assoc] using DL.bitmap i hi en)
    obtain ⟨t0,headPre,t0eq⟩:=splitChain leftSetup head
    have yes := headPre.continue _ (.seq run (.skip _))
    have yy : Executes n m rightProgram a v _ := yes
    refine ⟨v,_,pre.continue _ (.seq (.yes (a1 ▸ test.mpr en) yy) (.skip _)),by omega,?_,h'.trans gh,o'.trans o,c'.trans c⟩
    simpa [en,reg 209 (by decide) (by decide)] using flag
  · exact ⟨a,_,pre.continue _ (.seq (.no (by rw [a1];exact fun h=>en (test.mp h)) (.skip _)) (.skip _)),
      by omega,by simpa [en] using a209,h,o,c⟩

private lemma outerLoop (n L R rep touch mat : ℕ) (m : ℤ→ℤ) (s : State) (A B : ℕ→Cluster n) (E F : ℕ→Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (left : s.reg 207=(L:ℤ))
    (base : s.reg 208=(R:ℤ)) (repAt : s.reg 77=(rep:ℤ)) (touchAt : s.reg 79=(touch:ℤ)) (matAt : s.reg 80=(mat:ℤ))
    (DL : RowData n rep touch mat L s E A) (DR : RowData n rep touch mat R s F B) :
    ∃t k,Executes n m leftLoop s t k ∧ k≤9+n*(205+6*n+n*(275+340*n)) ∧
      t.reg 209=(if (List.range n).all (fun i=> !E i || (List.range n).all (fun j=> !F j || pass (A i) (B j))) then s.reg 209 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let ok := fun i => !E i || (List.range n).all (fun j=> !F j || pass (A i) (B j))
  let P := fun i (t:State) => t.reg 209=(if (List.range i).all ok then s.reg 209 else 0) ∧
    t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed
  obtain ⟨t,k,run,tm,res⟩:=Scene.GeometryTables.counted 210 795 64 n (200+6*n+n*(275+340*n)) leftBody s P
    (by decide) (by decide) (by decide) (by decide) size (by simp [P]) (by
      intro i u j v which good;rcases which with rfl|rfl <;> simpa [P,State.assign] using good) (by
      intro i hi u good fr idx
      obtain ⟨acc,h,o,c⟩:=good
      obtain ⟨v,l,ex,tm,flag,h',o',c'⟩:=outerStep n L R i rep touch mat m u A B E F hi ((fr 6 (by decide)).trans one)
        ((fr 64 (by decide)).trans size) ((fr 207 (by decide)).trans left) ((fr 208 (by decide)).trans base)
        idx ((fr 77 (by decide)).trans repAt) ((fr 79 (by decide)).trans touchAt) ((fr 80 (by decide)).trans matAt)
        (DL.keep h) (DR.keep h)
      refine ⟨v,l,ex,tm,?_,h'.trans h,o'.trans o,c'.trans c⟩
      change v.reg 209=(if (List.range (i+1)).all ok then s.reg 209 else 0)
      change v.reg 209=(if ok i then u.reg 209 else 0) at flag
      rw [flag,acc,List.range_succ,List.all_append]
      cases (List.range i).all ok <;> cases hbit : ok i <;> simp [hbit])
  exact ⟨t,k,run,by ring_nf at tm ⊢;exact tm,res⟩

private def fitsStart : List Program := [.op (.multiply 781 203 70),.op (.regular (.add 780 781 204)),
  .op (.multiply 779 780 64),.op (.regular (.copy 207 779)),.op (.multiply 788 205 70),
  .op (.regular (.add 787 788 206)),.op (.multiply 786 787 64),.op (.regular (.copy 208 786)),
  .op (.regular (.set 793 1)),.op (.regular (.copy 209 793))]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open Scene.CutTraversal
theorem solution (n M a b x y rep touch matrix : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (E F : ℕ→Bool) (A B : ℕ→Cluster n)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (slots : s.reg 70=(M:ℤ))
    (ra : s.reg 203=(a:ℤ)) (rx : s.reg 204=(x:ℤ)) (rb : s.reg 205=(b:ℤ)) (ry : s.reg 206=(y:ℤ))
    (repAt : s.reg 77=(rep:ℤ)) (touchAt : s.reg 79=(touch:ℤ)) (mat : s.reg 80=(matrix:ℤ))
    (enabledA : ∀i<n,(1 ≤ s.heap (rep+((a*M+x)*n+i)) ∧ 1 ≤ s.heap (touch+((a*M+x)*n+i))) ↔ E i=true)
    (enabledB : ∀j<n,(1 ≤ s.heap (rep+((b*M+y)*n+j)) ∧ 1 ≤ s.heap (touch+((b*M+y)*n+j))) ↔ F j=true)
    (bitmapA : ∀i<n,E i=true → ∀p:Fin n,s.heap (matrix+(((a*M+x)*n+i)*n+p.val))=if p∈A i then 1 else 0)
    (bitmapB : ∀j<n,F j=true → ∀p:Fin n,s.heap (matrix+(((b*M+y)*n+j)*n+p.val))=if p∈B j then 1 else 0) :
    ∃t k, Logical.Executes n m src_fits s t k ∧ k≤1000*(M+1)+1000*(n+1)^3 ∧
      t.reg 217=(if (List.range n).all (fun i=> !E i || (List.range n).all (fun j=>
        !F j || decide (Disjoint (A i) (B j) ∨ A i=B j))) then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let L := (a*M+x)*n
  let R := (b*M+y)*n
  let u := (((((((((s.assign 781 ((a*M:ℕ):ℤ)).assign 780 ((a*M+x:ℕ):ℤ)).assign 779 (L:ℤ)).assign 207 (L:ℤ)).assign 788 ((b*M:ℕ):ℤ)).assign 787 ((b*M+y:ℕ):ℤ)).assign 786 (R:ℤ)).assign 208 (R:ℤ)).assign 793 1).assign 209 1
  have head : Logical.Executes n m (chain fitsStart) s u (49+12*M+12*n) := by
    apply evalLine_sound
    simp [fitsStart,chain,evalLine,Operation.next,regularNext,u,L,R,Logical.State.assign,one,size,slots,ra,rx,rb,ry,
      show 0≤(a:ℤ)*M+x by positivity,show 0≤(b:ℤ)*M+y by positivity]
    all_goals omega
  have reg (j : ℕ) (h : writesReg j (chain fitsStart)=false) := head.preserves j h
  have D : RowData n rep touch matrix L u E A := ⟨enabledA,bitmapA⟩
  have D' : RowData n rep touch matrix R u F B := ⟨enabledB,bitmapB⟩
  obtain ⟨v,k,loop,tm,flag,h,o,c⟩:=outerLoop n L R rep touch matrix m u A B E F
    ((reg 6 (by decide)).trans one) ((reg 64 (by decide)).trans size) (by simp [u,Logical.State.assign])
    (by simp [u,Logical.State.assign]) ((reg 77 (by decide)).trans repAt) ((reg 79 (by decide)).trans touchAt)
    ((reg 80 (by decide)).trans mat) D D'
  obtain ⟨z,pre,zk⟩:=splitChain fitsStart head
  let t:=v.assign 217 (v.reg 209)
  have done_ : Logical.Executes n m (.op (.regular (.copy 217 209))) v t 1 := .op rfl
  refine ⟨t,_,pre.continue _ (.seq loop (.seq done_ (.skip _))),?_,?_,h,o,c⟩
  · calc _ ≤ (49+12*M+12*n)+(9+n*(205+6*n+n*(275+340*n)))+4 := by omega
         _ ≤ _ := by ring_nf;omega
  · have acc : u.reg 209=1 := by simp [u,Logical.State.assign]
    rw [acc] at flag
    exact flag

#print axioms solution
