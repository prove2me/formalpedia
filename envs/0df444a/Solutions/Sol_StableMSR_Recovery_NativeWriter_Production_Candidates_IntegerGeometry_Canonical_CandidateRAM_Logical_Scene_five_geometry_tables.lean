-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.five_geometry_tables
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T21:10:41.431136+00:00
-- url     : https://prove2.me/submissions/d473c106-ba66-4f2f-8cfb-405b71f57708

import Definitions.Def_StableMSR_RegionalGeometryTables
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_NetRAM_greedy_net_bitmap
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_representative_and_piece

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
set_option autoImplicit false
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables

def ownerStep := chain [.op (.fetch 693 71 198),
          .op (.regular (.copy 692 693)),
          .cond 6 692 (chain [.op (.regular (.copy 159 198)),
              .op (.regular (.copy 160 194)),
              src_imat,
              .op (.regular (.copy 697 161)),
              .op (.shift 700 195 1),
              .cond 697 700 (.op (.regular (.set 696 1))) (.op (.regular (.set 696 0))),
              .op (.regular (.copy 692 696))]) (.skip),
          .cond 6 692 (chain [.cond 197 198 (.op (.regular (.set 702 0))) (.op (.regular (.set 702 1))),
              .op (.regular (.copy 692 702))]) (.skip),
          .cond 6 692 (.op (.regular (.copy 197 198))) (.skip)]

def windowOps : List Program := [.op (.fetch 717 73 194),
          .op (.regular (.copy 716 717)),
          .cond 6 716 (chain [.op (.regular (.copy 159 198)),
              .op (.regular (.copy 160 194)),
              src_imat,
              .op (.regular (.copy 721 161)),
              .op (.shift 724 195 2),
              .cond 721 724 (.op (.regular (.set 720 1))) (.op (.regular (.set 720 0))),
              .op (.regular (.copy 716 720))]) (.skip),
          .cond 6 716 (chain [.op (.multiply 729 198 64),
              .op (.regular (.add 728 729 194)),
              .op (.regular (.set 733 1)),
              .op (.save 74 728 733)]) (.skip)]

def edgeOps : List Program := [.cond 194 198 (.cond 198 194 (.op (.regular (.set 735 0))) (.op (.regular (.set 735 1)))) (.op (.regular (.set 735 1))),
          .op (.regular (.copy 734 735)),
          .cond 6 734 (chain [.op (.regular (.copy 159 194)),
              .op (.regular (.copy 160 198)),
              src_imat,
              .op (.regular (.copy 739 161)),
              .op (.shift 742 195 3),
              .cond 739 742 (.op (.regular (.set 738 1))) (.op (.regular (.set 738 0))),
              .op (.regular (.copy 734 738))]) (.skip),
          .cond 6 734 (chain [.op (.regular (.copy 159 198)),
              .op (.regular (.copy 160 194)),
              src_imat,
              .op (.regular (.copy 745 161)),
              .op (.shift 748 195 3),
              .cond 745 748 (.op (.regular (.set 744 1))) (.op (.regular (.set 744 0))),
              .op (.regular (.copy 734 744))]) (.skip),
          .cond 6 734 (chain [.op (.multiply 753 194 64),
              .op (.regular (.add 752 753 198)),
              .op (.regular (.set 757 1)),
              .op (.save 75 752 757)]) (.skip)]

def finishOwner : List Program := [.cond 197 64 (.cond 64 197 (.op (.regular (.set 706 1))) (.op (.regular (.set 706 0)))) (.op (.regular (.set 706 0))),
      .cond 6 706 (.op (.regular (.copy 197 194))) (.skip),
      .op (.save 72 194 197)]

def pairStep := chain (windowOps ++ edgeOps)
def pointStep := chain ([.op (.regular (.copy 197 64)),forCount 198 691 64 ownerStep] ++ finishOwner ++ [forCount 198 715 64 pairStep])
def sweep := forCount 194 688 64 pointStep
theorem source_sweep : (listOf src_build_geometry)[23]? = some sweep := rfl

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
end

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
set_option autoImplicit false
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
/-- Registers outside the write set retain the values with which the loop started. -/
lemma outside_for {ix last len r : ℕ} {body : Program}
    (off : writesReg r (forCount ix last len body) = false) :
    r ≠ ix ∧ r ≠ last ∧ writesReg r body = false := by
  simpa [forCount,chain,writesReg,writesOp,and_assoc,and_left_comm,and_comm] using off

lemma counted {n : ℕ} {m : ℤ → ℤ} (ix last len count cap : ℕ) (body : Program)
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

/-- Minimum eligible index seen so far, with n as the sentinel. -/
def leastSeen (ok : ℕ → Bool) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k+1 => if ok k && decide (k < leastSeen ok n k) then k else leastSeen ok n k

lemma leastSeen_spec (ok : ℕ → Bool) (n k : ℕ) (hk : k ≤ n) :
    leastSeen ok n k ≤ n ∧
    (leastSeen ok n k < n → leastSeen ok n k < k ∧ ok (leastSeen ok n k) = true) ∧
    ∀ i < k, ok i = true → leastSeen ok n k ≤ i := by
  induction k with
  | zero => simp [leastSeen]
  | succ k ih =>
    obtain ⟨bn,hit,low⟩ := ih (by omega)
    simp only [leastSeen,Bool.and_eq_true,decide_eq_true_eq]
    split_ifs with take
    · refine ⟨by omega,fun _ => ⟨by omega,take.1⟩,?_⟩
      intro i hi yes
      by_cases eq : i = k
      · omega
      · have le := low i (by omega) yes; omega
    · refine ⟨bn,fun h => ⟨by have := (hit h).1; omega,(hit h).2⟩,?_⟩
      intro i hi yes
      by_cases eq : i = k
      · subst i; simp [yes] at take; omega
      · exact low i (by omega) yes

def nearAt (m : ℤ → ℤ) (heap : ℕ → ℤ) (n a p U j : ℕ) :=
  decide (1 ≤ heap (a+j) ∧ m (cell 6 (j*n+p)) ≤ 2*(U:ℤ))

theorem owner_step (n a p j U b : ℕ) (m : ℤ → ℤ) (s : State)
    (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ)) (base : s.reg 71=(a:ℤ))
    (pt : s.reg 194=(p:ℤ)) (ix : s.reg 198=(j:ℤ)) (unit' : s.reg 195=(U:ℤ))
    (best : s.reg 197=(b:ℤ)) :
    ∃ t k, Executes n m ownerStep s t k ∧ k ≤ 180+6*n ∧
      t.reg 197 = ((if nearAt m s.heap n a p U j && decide (j<b) then j else b : ℕ):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let q := cell 6 (j*n+p)
  have addr : q = -87-64*((j:ℤ)*n+p) := by simp [q,cell,word]; ring
  have raw : rawInput q = true := by
    have h : 0 ≤ (j:ℤ)*n := by positivity
    simp [q,cell,word,rawInput]; omega
  have h : ∃ t k,evalLine n m ownerStep s=some (t,k) ∧ k ≤ 180+6*n ∧
      t.reg 197 = ((if nearAt m s.heap n a p U j && decide (j<b) then j else b : ℕ):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    by_cases active : 1 ≤ s.heap (a+j) <;> by_cases near : m q ≤ 2*(U:ℤ) <;> by_cases earlier : j<b <;>
      simp [ownerStep,chain,evalLine,Operation.next,regularNext,State.assign,src_imat,one,sz,base,pt,ix,unit',best,
        show 0 ≤ (a:ℤ)+j by omega,show ((a:ℤ)+j).toNat=a+j by omega,←addr,raw,active,near,earlier,
        show ((b:ℤ)≤j) ↔ ¬ j<b by omega, nearAt,show cell 6 (j*n+p)=q from rfl] <;> omega
  obtain ⟨t,k,ev,tm,rest⟩ := h
  exact ⟨t,k,evalLine_sound _ _ _ _ ev,tm,rest⟩

theorem owner_scan (n a p U : ℕ) (m : ℤ → ℤ) (s : State)
    (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ)) (base : s.reg 71=(a:ℤ))
    (pt : s.reg 194=(p:ℤ)) (scale : s.reg 195=(U:ℤ)) (sentinel : s.reg 197=(n:ℤ)) :
    ∃ t k, Executes n m (forCount 198 691 64 ownerStep) s t k ∧ k ≤ 9+n*(185+6*n) ∧
      t.reg 197 = (leastSeen (nearAt m s.heap n a p U) n n : ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let P := fun j (u:State) => u.reg 197=(leastSeen (nearAt m s.heap n a p U) n j : ℤ) ∧
    u.heap=s.heap ∧ u.output=s.output ∧ u.closed=s.closed
  obtain ⟨t,k,run,tm,good⟩ := counted (n:=n) (m:=m) 198 691 64 n (180+6*n) ownerStep s P
    (by decide) (by decide) (by decide) (by decide) sz ⟨sentinel,rfl,rfl,rfl⟩
    (by rintro i u r v (rfl|rfl) h <;> exact h) (by
      intro j _ u ok fr idx
      obtain ⟨best,mem,out,cl⟩ := ok
      obtain ⟨t,k,run,tm,best',mem',out',cl'⟩ := owner_step n a p j U _ m u ((fr 6 (by decide)).trans one)
        ((fr 64 (by decide)).trans sz) ((fr 71 (by decide)).trans base) ((fr 194 (by decide)).trans pt) idx
        ((fr 195 (by decide)).trans scale) best
      refine ⟨t,k,run,tm,?_,mem'.trans mem,out'.trans out,cl'.trans cl⟩
      simpa only [leastSeen,mem] using best')
  exact ⟨t,k,run,by simpa only [show 180+6*n+5 = 185+6*n by omega] using tm,good⟩

lemma least_owner {n : ℕ} (m : ℤ → ℤ) (heap : ℕ → ℤ) (a : ℕ) (N : Cluster n) (p : Fin n)
    (bits : ∀ z : Fin n, 1 ≤ heap (a+z.val) ↔ z ∈ N) :
    let b := leastSeen (nearAt m heap n a p.val (unit n)) n n
    (if b=n then p.val else b) = (Bits.owner m N p).val := by
  let test := nearAt m heap n a p.val (unit n)
  let b := leastSeen test n n
  let C := N.filter fun z => m (address z p) ≤ 2*(unit n:ℤ)
  have yes (z : Fin n) : test z.val = true ↔ z ∈ C := by
    change _ ↔ z ∈ N.filter _
    rw [Finset.mem_filter]; simp only [test,nearAt,decide_eq_true_eq,bits,address]
  obtain ⟨bound,hit,lowest⟩ := leastSeen_spec test n n le_rfl
  change b ≤ n at bound
  change b < n → b < n ∧ test b = true at hit
  change ∀ i < n, test i = true → b ≤ i at lowest
  change (if b=n then p.val else b) = (Bits.owner m N p).val
  change (if b=n then p.val else b) = (if h : C.Nonempty then C.min' h else p).val
  by_cases existsPoint : C.Nonempty
  · let z := C.min' existsPoint
    have mem : z ∈ C := C.min'_mem existsPoint
    have le := lowest z.val z.isLt ((yes z).mpr mem)
    have lt : b < n := lt_of_le_of_lt le z.isLt
    let v : Fin n := ⟨b,lt⟩
    have rev : z ≤ v := C.min'_le v ((yes v).mp (hit lt).2)
    have eq : b=z.val := Nat.le_antisymm le rev
    simpa only [if_neg (Nat.ne_of_lt lt),dif_pos existsPoint] using eq
  · have eq : b=n := by
      by_contra ne
      have lt : b<n := by omega
      exact existsPoint ⟨⟨b,lt⟩,(yes ⟨b,lt⟩).mp (hit lt).2⟩
    simp only [eq,if_pos,dif_neg existsPoint]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
end

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
set_option autoImplicit false
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
def markIf (heap : ℕ → ℤ) (i : ℕ) (on : Bool) := if on then Function.update heap i 1 else heap

def winBit (n : ℕ) (m : ℤ → ℤ) (inside : Bool) (p a : ℕ) :=
  inside && decide (m (cell 6 (a*n+p)) ≤ 4*(unit n:ℤ))

def edgeBit (n : ℕ) (m : ℤ → ℤ) (p a : ℕ) :=
  decide (p ≠ a ∧ m (cell 6 (p*n+a)) ≤ 8*(unit n:ℤ) ∧ m (cell 6 (a*n+p)) ≤ 8*(unit n:ℤ))

lemma matrix_address (n i j : ℕ) : cell 6 (i*n+j) = -87-64*((i:ℤ)*n+j) := by
  simp [cell,word]; ring
lemma matrix_raw (n i j : ℕ) : rawInput (cell 6 (i*n+j)) = true := by
  have nn : 0 ≤ (i:ℤ)*n := by positivity
  simp [cell,word,rawInput]; omega

lemma indexed_nonneg (base n i j : ℕ) : 0 ≤ (base:ℤ)+((i:ℤ)*n+j) := by positivity
lemma indexed_nat (base n i j : ℕ) : ((base:ℤ)+((i:ℤ)*n+j)).toNat = base+(i*n+j) := by
  exact_mod_cast (Int.toNat_natCast (base+(i*n+j)))

theorem window_step (n B V p a : ℕ) (m : ℤ → ℤ) (s : State)
    (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ)) (piece : s.reg 73=(B:ℤ)) (win : s.reg 74=(V:ℤ))
    (pt : s.reg 194=(p:ℤ)) (ix : s.reg 198=(a:ℤ)) (scale : s.reg 195=(unit n:ℤ)) :
    ∃ t k, Executes n m (chain windowOps) s t k ∧ k ≤ 280+12*n ∧
      t.heap=markIf s.heap (V+(a*n+p)) (winBit n m (decide (1 ≤ s.heap (B+p))) p a) ∧
      t.output=s.output ∧ t.closed=s.closed := by
  have h : ∃ t k,evalLine n m (chain windowOps) s=some (t,k) ∧ k ≤ 280+12*n ∧
      t.heap=markIf s.heap (V+(a*n+p)) (winBit n m (decide (1 ≤ s.heap (B+p))) p a) ∧
      t.output=s.output ∧ t.closed=s.closed := by
    by_cases member : 1 ≤ s.heap (B+p) <;> by_cases near : m (cell 6 (a*n+p)) ≤ 4*(unit n:ℤ) <;>
      simp [windowOps,chain,evalLine,Operation.next,regularNext,State.assign,State.save,src_imat,one,sz,piece,win,pt,ix,scale,
        show 0 ≤ (B:ℤ)+p by omega,show ((B:ℤ)+p).toNat=B+p by omega,←matrix_address n a p,matrix_raw,member,near,
        indexed_nonneg V n a p,indexed_nat V n a p,winBit,markIf] <;> omega
  obtain ⟨t,k,ev,tm,res⟩ := h
  exact ⟨t,k,evalLine_sound _ _ _ _ ev,tm,res⟩

theorem edge_step (n E p a : ℕ) (m : ℤ → ℤ) (s : State)
    (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ)) (edge : s.reg 75=(E:ℤ))
    (pt : s.reg 194=(p:ℤ)) (ix : s.reg 198=(a:ℤ)) (scale : s.reg 195=(unit n:ℤ)) :
    ∃ t k, Executes n m (chain edgeOps) s t k ∧ k ≤ 310+18*n ∧
      t.heap=markIf s.heap (E+(p*n+a)) (edgeBit n m p a) ∧ t.output=s.output ∧ t.closed=s.closed := by
  have h : ∃ t k,evalLine n m (chain edgeOps) s=some (t,k) ∧ k ≤ 310+18*n ∧
      t.heap=markIf s.heap (E+(p*n+a)) (edgeBit n m p a) ∧ t.output=s.output ∧ t.closed=s.closed := by
    rcases lt_trichotomy p a with lt|eq|gt
    · by_cases near : m (cell 6 (p*n+a)) ≤ 8*(unit n:ℤ) <;> by_cases back : m (cell 6 (a*n+p)) ≤ 8*(unit n:ℤ) <;>
        simp [edgeOps,chain,evalLine,Operation.next,regularNext,State.assign,State.save,src_imat,one,sz,edge,pt,ix,scale,
          lt.le,not_le.mpr lt,ne_of_lt lt,←matrix_address n a p,←matrix_address n p a,matrix_raw,near,back,
          indexed_nonneg E n p a,indexed_nat E n p a,edgeBit,markIf] <;> omega
    · subst a; simp [edgeOps,chain,evalLine,Operation.next,regularNext,State.assign,one,sz,pt,ix,edgeBit,markIf] <;> omega
    · by_cases near : m (cell 6 (p*n+a)) ≤ 8*(unit n:ℤ) <;> by_cases back : m (cell 6 (a*n+p)) ≤ 8*(unit n:ℤ) <;>
        simp [edgeOps,chain,evalLine,Operation.next,regularNext,State.assign,State.save,src_imat,one,sz,edge,pt,ix,scale,
          gt.le,not_le.mpr gt,ne_of_gt gt,←matrix_address n a p,←matrix_address n p a,matrix_raw,near,back,
          indexed_nonneg E n p a,indexed_nat E n p a,edgeBit,markIf] <;> omega
  obtain ⟨t,k,ev,tm,res⟩ := h
  exact ⟨t,k,evalLine_sound _ _ _ _ ev,tm,res⟩

lemma mark_else {h : ℕ → ℤ} {a z : ℕ} {b : Bool} (ne : z ≠ a) : markIf h a b z=h z := by
  cases b <;> simp [markIf,Function.update_of_ne ne]
lemma mark_self (h : ℕ → ℤ) (a : ℕ) (b : Bool) : markIf h a b a = if b then 1 else h a := by
  cases b <;> simp [markIf]

lemma chain_both {n m} {l r : List Program} {s t u : State} {k j}
    (a : Executes n m (chain l) s t k) (b : Executes n m (chain r) t u j) :
    ∃ c, Executes n m (chain (l++r)) s u c ∧ c+1=k+j := by
  obtain ⟨c,run,eq⟩ := splitChain l a
  refine ⟨c+j,?_,by omega⟩
  simpa only [chain,List.foldr_append] using run.continue (chain r) b

/-- Linearization is injective on array columns smaller than the row length. -/
lemma flat_inj {n i j u v : ℕ} (hj : j<n) (hv : v<n) (eq : i*n+j=u*n+v) : i=u ∧ j=v := by
  rw [Nat.add_comm (i*n) j,Nat.add_comm (u*n) v] at eq
  constructor
  · simpa only [Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hj),Nat.div_eq_of_lt hj,Nat.div_eq_of_lt hv,Nat.zero_add]
      using congrArg (fun k => k/n) eq
  · simpa only [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hv]
      using congrArg (fun k => k%n) eq

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
end

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
set_option autoImplicit false
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
/-- The window matrix is indexed by (centre, point), the edge matrix by (point, centre). -/
def winAddr (n p a : ℕ) := 3*n+(a*n+p)
def edgeAddr (n p a : ℕ) := 3*n+n*n+(p*n+a)

def Hit (n : ℕ) (m : ℤ → ℤ) (inside : Bool) (p a z : ℕ) : Prop :=
  (z=winAddr n p a ∧ winBit n m inside p a=true) ∨ (z=edgeAddr n p a ∧ edgeBit n m p a=true)

noncomputable def marked (heap : ℕ → ℤ) (S : ℕ → Prop) (z : ℕ) : ℤ :=
  if S z then 1 else heap z

lemma mark_apply (h : ℕ → ℤ) (j q : ℕ) (b : Bool) :
    markIf h j b q = if q=j ∧ b=true then 1 else h q := by
  cases b <;> by_cases eq : q=j <;> simp [markIf,eq,Function.update_apply]

lemma hit_lower {n m b p a z} (h : Hit n m b p a z) : 3*n ≤ z := by
  rcases h with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp [winAddr,edgeAddr] <;> omega

lemma flat_bound {n p a : ℕ} (hp : p<n) (ha : a<n) : a*n+p<n*n := by
  have h := Nat.mul_le_mul_right n (show a+1 ≤ n by omega)
  rw [Nat.succ_mul] at h; omega

lemma win_edge_disjoint {n p a q v : ℕ} (hp : p<n) (ha : a<n) : winAddr n p a ≠ edgeAddr n q v := by
  have := flat_bound hp ha; unfold winAddr edgeAddr; omega

lemma hit_upper {n m b p a z} (hp : p<n) (ha : a<n) (h : Hit n m b p a z) : z < 3*n+2*(n*n) := by
  have h₁ := flat_bound hp ha
  have h₂ := flat_bound ha hp
  rcases h with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp only [winAddr,edgeAddr] <;> omega

/-- Extend a union of marked cells by one iteration. -/
lemma marked_succ (heap : ℕ → ℤ) (F : ℕ → ℕ → Prop) (i : ℕ) :
    marked (marked heap (fun z => ∃ j < i,F j z)) (F i) = marked heap (fun z => ∃ j < i+1,F j z) := by
  funext z
  have eq : (∃ j < i+1,F j z) ↔ F i z ∨ ∃ j < i,F j z := by
    constructor
    · rintro ⟨j,h,w⟩; by_cases same : j=i
      · exact .inl (same ▸ w)
      · exact .inr ⟨j,by omega,w⟩
    · rintro (w|⟨j,h,w⟩)
      · exact ⟨i,by omega,w⟩
      · exact ⟨j,by omega,w⟩
  simp only [marked,eq]
  by_cases h : F i z <;> simp only [h,if_true,if_false,true_or,false_or] <;> split_ifs <;> rfl

structure Control (n : ℕ) (s : State) : Prop where
  one : s.reg 6=1
  size : s.reg 64=(n:ℤ)
  active : s.reg 71=0
  owners : s.reg 72=(n:ℤ)
  piece : s.reg 73=((2*n:ℕ):ℤ)
  windows : s.reg 74=((3*n:ℕ):ℤ)
  edges : s.reg 75=((3*n+n*n:ℕ):ℤ)
  scale : s.reg 195=(unit n:ℤ)

lemma Control.transport {n s t} (h : Control n s)
    (frame : ∀ j ∈ [6,64,71,72,73,74,75,195], t.reg j=s.reg j) : Control n t :=
  ⟨(frame _ (by decide)).trans h.one,(frame _ (by decide)).trans h.size,
   (frame _ (by decide)).trans h.active,(frame _ (by decide)).trans h.owners,
   (frame _ (by decide)).trans h.piece,(frame _ (by decide)).trans h.windows,
   (frame _ (by decide)).trans h.edges,(frame _ (by decide)).trans h.scale⟩

theorem pair_step (n p a : ℕ) (m : ℤ → ℤ) (s : State) (ctrl : Control n s)
    (pt : s.reg 194=(p:ℤ)) (ix : s.reg 198=(a:ℤ)) :
    ∃ t k, Executes n m pairStep s t k ∧ k ≤ 590+30*n ∧
      t.heap=marked s.heap (Hit n m (decide (1 ≤ s.heap (2*n+p))) p a) ∧
      t.output=s.output ∧ t.closed=s.closed := by
  obtain ⟨v,k,w,wt,win,wo,wc⟩ := window_step n (2*n) (3*n) p a m s ctrl.one ctrl.size ctrl.piece ctrl.windows pt ix ctrl.scale
  obtain ⟨t,j,e,et,edge,eo,ec⟩ := edge_step n (3*n+n*n) p a m v
    ((w.preserves 6 (by decide)).trans ctrl.one) ((w.preserves 64 (by decide)).trans ctrl.size)
    ((w.preserves 75 (by decide)).trans ctrl.edges) ((w.preserves 194 (by decide)).trans pt)
    ((w.preserves 198 (by decide)).trans ix) ((w.preserves 195 (by decide)).trans ctrl.scale)
  obtain ⟨c,run,charge⟩ := chain_both w e
  refine ⟨t,c,run,by omega,?_,eo.trans wo,ec.trans wc⟩
  funext z
  rw [edge,win,mark_apply,mark_apply]
  unfold marked Hit winAddr edgeAddr
  split_ifs <;> tauto

theorem pair_loop (n p : ℕ) (m : ℤ → ℤ) (s : State) (hp : p<n) (ctrl : Control n s) (pt : s.reg 194=(p:ℤ)) :
    let inside := decide (1 ≤ s.heap (2*n+p))
    ∃ t k, Executes n m (forCount 198 715 64 pairStep) s t k ∧ k ≤ 9+n*(595+30*n) ∧
      t.heap=marked s.heap (fun z => ∃ a<n,Hit n m inside p a z) ∧ t.output=s.output ∧ t.closed=s.closed := by
  let inside := decide (1 ≤ s.heap (2*n+p))
  let P := fun i (u:State) => u.heap=marked s.heap (fun z => ∃ a < i,Hit n m inside p a z) ∧ u.output=s.output ∧ u.closed=s.closed
  obtain ⟨t,k,run,tm,good⟩ := counted (n:=n) (m:=m) 198 715 64 n (590+30*n) pairStep s P
    (by decide) (by decide) (by decide) (by decide) ctrl.size
    ⟨by funext z; simp [marked],rfl,rfl⟩ (by rintro i u r v _ h; exact h) (by
      intro i hi u ok fr ix
      have cu : Control n u := ctrl.transport (by
        intro reg member
        simp at member
        rcases member with eq|eq|eq|eq|eq|eq|eq|eq <;> subst reg <;> exact fr _ (by decide))
      obtain ⟨v,k,ex,time,mem,out,cl⟩ := pair_step n p i m u cu ((fr 194 (by decide)).trans pt) ix
      have piece : u.heap (2*n+p)=s.heap (2*n+p) := by
        rw [ok.1]; apply if_neg; rintro ⟨a,_,h⟩; have := hit_lower h; omega
      refine ⟨v,k,ex,time,?_,out.trans ok.2.1,cl.trans ok.2.2⟩
      rw [mem,piece,ok.1]; exact marked_succ s.heap (fun a => Hit n m inside p a) i)
  exact ⟨t,k,run,by simpa only [show 590+30*n+5=595+30*n by omega] using tm,good⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
end

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
set_option autoImplicit false
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
/-- Use the fallback point on an empty search or when an index is out of range. -/
def ownerIndex {n : ℕ} (m : ℤ → ℤ) (N : Cluster n) (p : ℕ) : ℕ :=
  if hp : p<n then (Bits.owner m N ⟨p,hp⟩).val else p

def inPiece {n : ℕ} (W : Cluster n) (p : ℕ) :=
  if hp : p<n then decide ((⟨p,hp⟩ : Fin n)∈W) else false

theorem finish_owner (n p b : ℕ) (m : ℤ → ℤ) (s : State) (bn : b ≤ n)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (base : s.reg 72=(n:ℤ))
    (pt : s.reg 194=(p:ℤ)) (best : s.reg 197=(b:ℤ)) :
    ∃ t k, Executes n m (chain finishOwner) s t k ∧ k ≤ 80 ∧
      t.heap=Function.update s.heap (n+p) ((if b=n then p else b : ℕ):ℤ) ∧
      t.output=s.output ∧ t.closed=s.closed := by
  have h : ∃ t k,evalLine n m (chain finishOwner) s=some (t,k) ∧ k ≤ 80 ∧
      t.heap=Function.update s.heap (n+p) ((if b=n then p else b : ℕ):ℤ) ∧
      t.output=s.output ∧ t.closed=s.closed := by
    by_cases eq : b=n
    · subst b; simp [finishOwner,chain,evalLine,Operation.next,regularNext,State.assign,State.save,one,size,base,pt,best,
        show 0 ≤ (n:ℤ)+p by omega,show ((n:ℤ)+p).toNat=n+p by omega]
    · simp [finishOwner,chain,evalLine,Operation.next,regularNext,State.assign,State.save,one,size,base,pt,best,
        bn,show ¬n≤b by omega,eq,show 0 ≤ (n:ℤ)+p by omega,show ((n:ℤ)+p).toNat=n+p by omega]
  obtain ⟨t,k,ev,tm,res⟩ := h
  exact ⟨t,k,evalLine_sound _ _ _ _ ev,tm,res⟩

theorem point_step {n : ℕ} (m : ℤ → ℤ) (N W : Cluster n) (p : Fin n) (s : State)
    (ctrl : Control n s) (idx : s.reg 194=(p.val:ℤ))
    (active : ∀ z : Fin n, 1 ≤ s.heap z.val ↔ z∈N)
    (piece : decide (1 ≤ s.heap (2*n+p.val)) = inPiece W p.val) :
    ∃ t k, Executes n m pointStep s t k ∧ k ≤ 1100*(n+1)^2 ∧
      t.heap=marked (Function.update s.heap (n+p.val) (ownerIndex m N p.val : ℤ))
        (fun z => ∃ a < n, Hit n m (inPiece W p.val) p.val a z) ∧ t.output=s.output ∧ t.closed=s.closed := by
  let u := s.assign 197 (n:ℤ)
  have reset : Executes n m (.op (.regular (.copy 197 64))) s u 1 := by
    apply Executes.op; simp [regularNext,Operation.next,ctrl.size,u]
  let b := leastSeen (nearAt m s.heap n 0 p.val (unit n)) n n
  obtain ⟨v,j,scan,jt,best,vh,vo,vc⟩ := owner_scan n 0 p.val (unit n) m u ctrl.one ctrl.size ctrl.active idx ctrl.scale
    (by simp [u,State.assign])
  have b_le : b ≤ n := (leastSeen_spec _ _ _ le_rfl).1
  obtain ⟨y,l,finish,lt,yh,yo,yc⟩ := finish_owner n p.val b m v b_le ((scan.preserves 6 (by decide)).trans ctrl.one)
    ((scan.preserves 64 (by decide)).trans ctrl.size) ((scan.preserves 72 (by decide)).trans ctrl.owners)
    ((scan.preserves 194 (by decide)).trans idx) best
  have cf : Control n y := ctrl.transport (by
    intro r hr
    simp at hr
    rcases hr with hr|hr|hr|hr|hr|hr|hr|hr <;> subst r <;>
      exact (finish.preserves _ (by decide)).trans ((scan.preserves _ (by decide)).trans rfl))
  have pi := (finish.preserves 194 (by decide)).trans ((scan.preserves 194 (by decide)).trans idx)
  obtain ⟨t,k,pairs,kt,th,to',tc⟩ := pair_loop n p.val m y p.isLt cf pi
  obtain ⟨z,tail,zt⟩ := chain_both (r:=[forCount 198 715 64 pairStep]) finish (Executes.seq pairs (Executes.skip t) : Executes n m (chain [forCount 198 715 64 pairStep]) y t _)
  have run : Executes n m pointStep s t _ := Executes.seq reset (Executes.seq scan tail)
  have owner : (if b=n then p.val else b) = ownerIndex m N p.val := by
    simpa only [ownerIndex,dif_pos p.isLt] using least_owner m s.heap 0 N p (by simpa only [Nat.zero_add] using active)
  have written : y.heap = Function.update s.heap (n+p.val) (ownerIndex m N p.val:ℤ) := by rw [yh,vh,owner]; rfl
  have untouched : y.heap (2*n+p.val) = s.heap (2*n+p.val) := by
    rw [written,Function.update_of_ne (by have := p.isLt; omega)]
  refine ⟨t,_,run,?_,?_,to'.trans (yo.trans vo),tc.trans (yc.trans vc)⟩
  · ring_nf at jt kt ⊢ <;> omega
  · simpa only [untouched,piece,written] using th

/-- After i points, owners for indices below i and all visited positive matrix
entries have been installed. All other words retain their entry values. -/
noncomputable def after {n : ℕ} (m : ℤ → ℤ) (N W : Cluster n) (heap : ℕ → ℤ) (i z : ℕ) : ℤ :=
  if ∃ p < i, ∃ a < n,Hit n m (inPiece W p) p a z then 1
  else if n ≤ z ∧ z<n+i then (ownerIndex m N (z-n):ℤ) else heap z

lemma after_small {n : ℕ} (m : ℤ → ℤ) (N W : Cluster n) (heap : ℕ → ℤ) (i z : ℕ) (hi : i ≤ n)
    (h : z<n ∨ (2*n ≤ z ∧ z<3*n)) : after m N W heap i z=heap z := by
  unfold after
  rw [if_neg (by rintro ⟨_,_,_,_,hit⟩; have := hit_lower hit; omega),if_neg (by omega)]

lemma after_succ {n : ℕ} (m : ℤ → ℤ) (N W : Cluster n) (heap : ℕ → ℤ) (i : ℕ) (hi : i<n) :
    marked (Function.update (after m N W heap i) (n+i) (ownerIndex m N i : ℤ))
      (fun z => ∃ a < n,Hit n m (inPiece W i) i a z) = after m N W heap (i+1) := by
  funext z
  let H := fun p => ∃ a < n,Hit n m (inPiece W p) p a z
  have split : (∃ p < i+1,H p) ↔ H i ∨ ∃ p < i,H p := by
    constructor
    · rintro ⟨p,h,w⟩; by_cases same : p=i
      · exact .inl (same ▸ w)
      · exact .inr ⟨p,by omega,w⟩
    · rintro (w|⟨p,h,w⟩)
      · exact ⟨i,by omega,w⟩
      · exact ⟨p,by omega,w⟩
  by_cases atOwner : z=n+i
  · subst z
    have empty (p : ℕ) : ¬H p := by rintro ⟨a,_,h⟩; have := hit_lower h; omega
    have all : ¬∃ p < i+1,H p := by rintro ⟨p,_,h⟩; exact empty p h
    dsimp only [H] at empty all
    simp only [marked,after,if_neg (empty i),Function.update_self,if_neg all,
      if_pos (show n≤n+i ∧ n+i<n+(i+1) by omega),Nat.add_sub_cancel_left]
  · have range : (n ≤ z ∧ z<n+(i+1)) ↔ n ≤ z ∧ z<n+i := by omega
    dsimp only [H] at split
    simp only [marked,after,Function.update_of_ne atOwner,split,range]
    by_cases h : H i <;> by_cases old : ∃ p < i,H p <;>
      dsimp only [H] at h old <;> simp only [h,old,if_true,if_false,true_or,false_or] <;> split_ifs <;> rfl

theorem sweep_exec {n : ℕ} (m : ℤ → ℤ) (N W : Cluster n) (s : State) (ctrl : Control n s)
    (active : ∀ z : Fin n, 1 ≤ s.heap z.val ↔ z∈N)
    (piece : ∀ z : Fin n, decide (1 ≤ s.heap (2*n+z.val)) = inPiece W z.val) :
    ∃ t k, Executes n m sweep s t k ∧ k ≤ 9+n*(1100*(n+1)^2+5) ∧
      t.heap=after m N W s.heap n ∧ t.output=s.output ∧ t.closed=s.closed := by
  let P := fun i (u:State) => u.heap=after m N W s.heap i ∧ u.output=s.output ∧ u.closed=s.closed
  obtain ⟨t,k,run,tm,good⟩ := counted (n:=n) (m:=m) 194 688 64 n (1100*(n+1)^2) pointStep s P
    (by decide) (by decide) (by decide) (by decide) ctrl.size
    ⟨by funext z; simp [after],rfl,rfl⟩ (by rintro i u r v _ h; exact h) (by
      intro i hi u ok fr idx
      let p : Fin n := ⟨i,hi⟩
      have cu : Control n u := ctrl.transport (by
        intro reg member
        simp at member
        rcases member with eq|eq|eq|eq|eq|eq|eq|eq <;> subst reg <;> exact fr _ (by decide))
      have live (v:Fin n) : 1 ≤ u.heap v.val ↔ v∈N := by rw [ok.1,after_small _ _ _ _ _ _ hi.le (.inl v.isLt)]; exact active v
      have member : decide (1 ≤ u.heap (2*n+p.val))=inPiece W p.val := by
        rw [ok.1,after_small _ _ _ _ _ _ hi.le (.inr (by dsimp [p]; omega))]; exact piece p
      obtain ⟨v,k,ex,tm,h,o,c⟩ := point_step m N W p u cu idx live member
      exact ⟨v,k,ex,tm,by rw [h,ok.1]; exact after_succ _ _ _ _ _ hi,o.trans ok.2.1,c.trans ok.2.2⟩)
  exact ⟨t,k,run,tm,good⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
end

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
set_option autoImplicit false
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
lemma all_window_hits {n : ℕ} (m : ℤ → ℤ) (W : Cluster n) (p a : Fin n) :
    (∃ i < n, ∃ j < n,Hit n m (inPiece W i) i j (winAddr n p.val a.val)) ↔ p ∈ Bits.win m W a := by
  constructor
  · rintro ⟨i,hi,j,hj,⟨eq,b⟩|⟨eq,_⟩⟩
    · have e : a.val*n+p.val=j*n+i := Nat.add_left_cancel eq
      obtain ⟨rfl',rfl''⟩ := flat_inj p.isLt hi e
      subst i; subst j
      apply Finset.mem_filter.mpr
      simpa [winBit,inPiece,p.isLt,address] using b
    · exact (win_edge_disjoint p.isLt a.isLt eq).elim
  · intro member
    refine ⟨p.val,p.isLt,a.val,a.isLt,.inl ⟨rfl,?_⟩⟩
    have parts := Finset.mem_filter.mp member
    simpa [winBit,inPiece,p.isLt,address] using parts

lemma all_edge_hits {n : ℕ} (m : ℤ → ℤ) (W : Cluster n) (p a : Fin n) :
    (∃ i < n, ∃ j < n,Hit n m (inPiece W i) i j (edgeAddr n p.val a.val)) ↔
      p≠a ∧ m (address p a) ≤ 8*(unit n:ℤ) ∧ m (address a p) ≤ 8*(unit n:ℤ) := by
  constructor
  · rintro ⟨i,hi,j,hj,⟨eq,_⟩|⟨eq,b⟩⟩
    · exact (win_edge_disjoint hi hj eq.symm).elim
    · have e : p.val*n+a.val=i*n+j := Nat.add_left_cancel eq
      obtain ⟨ep,ea⟩ := flat_inj a.isLt hj e
      subst i; subst j
      simpa [edgeBit,address,Fin.val_inj] using b
  · intro edge
    refine ⟨p.val,p.isLt,a.val,a.isLt,.inr ⟨rfl,?_⟩⟩
    simpa [edgeBit,address,Fin.val_inj] using edge

lemma after_owner {n : ℕ} (m : ℤ → ℤ) (N W : Cluster n) (heap : ℕ → ℤ) (p : Fin n) :
    after m N W heap n (n+p.val)=(ownerIndex m N p.val:ℤ) := by
  unfold after
  rw [if_neg (by rintro ⟨i,hi,j,hj,b⟩; have := hit_lower b; have := p.isLt; omega),
      if_pos (by have := p.isLt; omega),Nat.add_sub_cancel_left]

lemma after_window {n : ℕ} (m : ℤ → ℤ) (N W : Cluster n) (heap : ℕ → ℤ) (p a : Fin n)
    (zero : heap (winAddr n p.val a.val)=0) :
    after m N W heap n (winAddr n p.val a.val) = if p∈Bits.win m W a then 1 else 0 := by
  unfold after
  have out : ¬(n ≤ winAddr n p.val a.val ∧ winAddr n p.val a.val<n+n) := by unfold winAddr; omega
  rw [if_neg out,zero]
  by_cases hit : p∈Bits.win m W a
  · rw [if_pos ((all_window_hits m W p a).mpr hit),if_pos hit]
  · rw [if_neg (fun h => hit ((all_window_hits m W p a).mp h)),if_neg hit]

lemma after_edge {n : ℕ} (m : ℤ → ℤ) (N W : Cluster n) (heap : ℕ → ℤ) (p a : Fin n)
    (zero : heap (edgeAddr n p.val a.val)=0) :
    after m N W heap n (edgeAddr n p.val a.val) =
      if p≠a ∧ m (address p a) ≤ 8*(unit n:ℤ) ∧ m (address a p) ≤ 8*(unit n:ℤ) then 1 else 0 := by
  unfold after
  have out : ¬(n ≤ edgeAddr n p.val a.val ∧ edgeAddr n p.val a.val<n+n) := by unfold edgeAddr; omega
  rw [if_neg out,zero]
  by_cases hit : p≠a ∧ m (address p a) ≤ 8*(unit n:ℤ) ∧ m (address a p) ≤ 8*(unit n:ℤ)
  · rw [if_pos ((all_edge_hits m W p a).mpr hit),if_pos hit]
  · rw [if_neg (fun h => hit ((all_edge_hits m W p a).mp h)),if_neg hit]

lemma after_frame {n : ℕ} (m : ℤ → ℤ) (N W : Cluster n) (heap : ℕ → ℤ) (q : ℕ)
    (lo : 3*n+2*(n*n) ≤ q) : after m N W heap n q=heap q := by
  unfold after
  rw [if_neg (by rintro ⟨i,hi,j,hj,h⟩; have := hit_upper hi hj h; omega),if_neg (by omega)]

lemma execution_state_unique {n m p s t k} (run : Executes n m p s t k) {v j} (other : Executes n m p s v j) : t=v := by
  induction run generalizing v j with
  | skip => cases other; rfl
  | op eq => cases other with | op eq' => rw [eq] at eq'; exact congrArg Prod.fst (Option.some.inj eq')
  | seq a b ia ib => cases other with | seq c d => obtain rfl := ia c; exact ib d
  | yes h ex ih => cases other with | yes _ e => exact ih e | no hn _ => contradiction
  | no h ex ih => cases other with | yes hn _ => contradiction | no _ e => exact ih e
  | stop h => cases other with | stop => rfl | more yes _ _ => contradiction
  | more h a b ia ib => cases other with | stop no => contradiction | more _ c d => obtain rfl := ia c; exact ib d

lemma after_prefix {n m ps s v k} (pr : PrefixRun n m ps s v k) (tail : Program) {t f}
    (run : Executes n m (ps.foldr Program.seq tail) s t f) : ∃ c, Executes n m tail v t c := by
  induction pr generalizing f with
  | nil => exact ⟨f,run⟩
  | cons first _ ih => cases run with | seq h rest => obtain rfl := execution_state_unique first h; exact ih rest

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
end

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
set_option autoImplicit false
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
lemma untouched_controls (j : ℕ) (hj : j=6 ∨ j=7 ∨ j=8 ∨ (64≤j ∧ j≤82)) :
    writesReg j Scene.geometryPrefix = false := by
  rcases hj with rfl|rfl|rfl|⟨lo,hi⟩ <;> (first | decide | interval_cases j <;> decide)

theorem build_geometry_image (x:World) (m:Store) (r h w:ℕ) (s:Logical.State)
    (hn:0<x.n) (hr:r<x.rows*x.n) (ready:Ready x m) (prepared:Logical.Prepared x.n r h w s) :
    ∃t k,Logical.Executes x.n m.imem Scene.geometryPrefix s t k ∧
      k ≤ 350*x.cap + 2000*(x.n+1)^3 ∧
      Scene.GeometryImage m.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h s t := by
  let W := WindowProfiles.piece x (r/x.n) (r%x.n)
  let N := Bits.net m.imem W
  let o := offsets x.n (sizes x.n h)
  obtain ⟨v,j,netRun,netTime,A,B,netFrame,vo,vc⟩ := Scene.NetRAM.greedy_net_bitmap x m r h w s hn hr ready prepared
  obtain ⟨one,zero,sz,slot,hh,ww,H,rows,M,r82,top,ptrs,fresh,output,closed⟩ := prepared
  obtain ⟨u,k,opening,_,_,_,_,_,uscale,_,_,_,_⟩ :=
    Scene.representative_and_piece x.n r m.imem x.mem s hn one sz slot ready.2
  obtain ⟨k',pre,_⟩ := splitChain ((listOf src_build_geometry).take 22) opening
  obtain ⟨q,last⟩ := after_prefix pre (chain (((listOf src_build_geometry).drop 22).take 1)) netRun
  have vscale := (last.preserves 195 (by decide)).trans uscale
  have p0 : cursorAt o 0=0 := rfl
  have p1 : cursorAt o 1=x.n := by simp [o,cursorAt,offsets]
  have p2 : cursorAt o 2=2*x.n := by simp [o,cursorAt,offsets]; omega
  have p3 : cursorAt o 3=3*x.n := by simp [o,cursorAt,offsets]; omega
  have p4 : cursorAt o 4=3*x.n+x.n*x.n := by simp [o,cursorAt,offsets]; omega
  have p5 : cursorAt o 5=3*x.n+2*(x.n*x.n) := by simp [o,cursorAt,offsets]; omega
  have bound : 3*x.n+2*(x.n*x.n) ≤ cursorAt o 11 := by simp [o,cursorAt,offsets]; omega
  have ctrl : Control x.n v := by
    refine ⟨(netRun.preserves 6 (by decide)).trans one,(netRun.preserves 64 (by decide)).trans sz,?_,?_,?_,?_,?_,vscale⟩
    · have hp := ptrs (⟨0,by decide⟩:Fin 11)
      change s.reg 71=(cursorAt o 0:ℤ) at hp
      rw [p0] at hp
      exact (netRun.preserves 71 (by decide)).trans hp
    · have hp := ptrs (⟨1,by decide⟩:Fin 11)
      change s.reg 72=(cursorAt o 1:ℤ) at hp
      rw [p1] at hp
      exact (netRun.preserves 72 (by decide)).trans hp
    · have hp := ptrs (⟨2,by decide⟩:Fin 11)
      change s.reg 73=(cursorAt o 2:ℤ) at hp
      rw [p2] at hp
      exact (netRun.preserves 73 (by decide)).trans hp
    · have hp := ptrs (⟨3,by decide⟩:Fin 11)
      change s.reg 74=(cursorAt o 3:ℤ) at hp
      rw [p3] at hp
      exact (netRun.preserves 74 (by decide)).trans hp
    · have hp := ptrs (⟨4,by decide⟩:Fin 11)
      change s.reg 75=(cursorAt o 4:ℤ) at hp
      rw [p4] at hp
      exact (netRun.preserves 75 (by decide)).trans hp
  dsimp only [o] at p0 p1 p2 p3 p4 p5
  have abits (p:Fin x.n) : v.heap p.val = if p∈N then 1 else 0 := by
    simpa only [p0,zero_add] using A p
  have bbits (p:Fin x.n) : v.heap (2*x.n+p.val) = if p∈W then 1 else 0 := by
    simpa only [p2] using B p
  have active (p:Fin x.n) : 1 ≤ v.heap p.val ↔ p∈N := by rw [abits]; by_cases hp:p∈N <;> simp [hp]
  have piece (p:Fin x.n) : decide (1 ≤ v.heap (2*x.n+p.val))=inPiece W p.val := by
    rw [bbits]; by_cases hp:p∈W <;> simp [hp,inPiece,p.isLt]
  obtain ⟨t,l,sweepRun,st,mem,tout,tcl⟩ := sweep_exec m.imem N W v ctrl active piece
  obtain ⟨z,netPrefix,charge⟩ := splitChain ((listOf src_build_geometry).take 23) netRun
  have full : Executes x.n m.imem Scene.geometryPrefix s t _ :=
    netPrefix.continue (.seq sweep .skip) (.seq sweepRun (.skip t))
  have old (a:ℕ) (lo:3*x.n≤a) : v.heap a=s.heap a :=
    netFrame a (by change a<cursorAt o 0 ∨ cursorAt o 0+x.n≤a; rw [p0]; omega)
      (by change a<cursorAt o 2 ∨ cursorAt o 2+x.n≤a; rw [p2]; omega)
  have cleared (a:ℕ) (lo:3*x.n≤a) (hi:a<3*x.n+2*(x.n*x.n)) : v.heap a=0 :=
    (old a lo).trans (fresh a (lt_of_lt_of_le hi bound))
  refine ⟨t,_,full,?_,?_⟩
  · ring_nf at netTime st ⊢ <;> omega
  constructor
  · intro a ha; exact full.preserves a (untouched_controls a ha)
  · exact (sweepRun.preserves 195 (by decide)).trans vscale
  · intro p
    rw [mem,p0,zero_add,after_small _ _ _ _ _ _ (le_refl _) (.inl p.isLt)]
    exact abits p
  · intro p
    rw [mem,p1,after_owner]
    simp only [ownerIndex,dif_pos p.isLt] <;> rfl
  · intro p
    rw [mem,p2,after_small _ _ _ _ _ _ (le_refl _) (.inr (by have := p.isLt; omega))]
    exact bbits p
  · intro a p
    rw [mem,p3]
    apply after_window
    apply cleared <;> unfold winAddr <;> have := flat_bound p.isLt a.isLt <;> omega
  · intro p a
    rw [mem,p4]
    apply after_edge
    apply cleared <;> unfold edgeAddr <;> have := flat_bound a.isLt p.isLt <;> omega
  · intro a ha
    rw [p5] at ha
    rw [mem,after_frame _ _ _ _ _ ha]
    exact old a (by omega)
  · exact tout.trans vo
  · exact tcl.trans vc

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
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
theorem solution (x:World) (m:Store) (r h w:ℕ) (s:Logical.State)
    (hn:0<x.n) (hr:r<x.rows*x.n) (ready:Ready x m) (prepared:Logical.Prepared x.n r h w s) :
    ∃t k,Logical.Executes x.n m.imem Scene.geometryPrefix s t k ∧
      k ≤ 350*x.cap + 2000*(x.n+1)^3 ∧
      Scene.GeometryImage m.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h s t := Scene.GeometryTables.build_geometry_image x m r h w s hn hr ready prepared
