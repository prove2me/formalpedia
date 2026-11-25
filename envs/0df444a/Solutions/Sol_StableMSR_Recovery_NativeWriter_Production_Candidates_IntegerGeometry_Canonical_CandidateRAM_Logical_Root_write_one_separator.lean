-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.write_one_separator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T12:54:32.276664+00:00
-- url     : https://prove2.me/submissions/0910af8b-7f65-4b75-8c46-3872abdae167
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_StableMSR_SeparatorVisits
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_ComponentScan_connected_component_bitmap
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_matrix_and_row_scans
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_write_component_representative
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

def forSetup (ix last len:ℕ) (s:State) := let u:=s.assign ix 0; let v:=u.assign last (u.reg len);v.assign last (v.reg last-1)
theorem source_for {N:ℕ} {input:ℤ → ℤ} (ix last len n cap:ℕ) (body:Program) (P:ℕ→State→Prop)
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


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables

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
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open SingleCircuit TightLanguage SeparatorLevels
set_option maxRecDepth 35000
set_option maxHeartbeats 6000000

private def makeRow : List Program := [.op (.alloc 1030 64),.op (.regular (.copy 244 1030))]
private def fillPoint := chain [.op (.fetch 1035 71 245), .op (.regular (.copy 1034 1035)),
  .cond 6 1034 (chain [.op (.fetch 1039 241 245),
    .cond 6 1039 (.op (.regular (.set 1038 0))) (.op (.regular (.set 1038 1))),
    .op (.regular (.copy 1034 1038))]) .skip,
  .cond 6 1034 (chain [.op (.regular (.set 1045 1)),.op (.save 244 245 1045)]) .skip]
private def setAllowed := chain (makeRow++[forCount 245 1033 64 fillPoint])
private def setSeed : List Program := [.op (.regular (.copy 132 244)),.op (.regular (.copy 133 246))]
private def setFirst : List Program := [.op (.regular (.copy 1051 138)),.op (.regular (.copy 247 1051)),
  .op (.regular (.copy 144 247))]
private def testHead : List Program := [.op (.regular (.copy 1055 147)),.cond 1055 246
  (.cond 246 1055 (.op (.regular (.set 1054 1))) (.op (.regular (.set 1054 0)))) (.op (.regular (.set 1054 0)))]
private def readComponent := chain (setSeed++[src_component]++setFirst++[src_first]++testHead)
private def acceptSeed := chain (setSeed++[src_component]++setFirst++[src_first]++testHead++[.cond 6 1054 representativeWork .skip])
private def readAllowed : Program := .op (.fetch 1048 244 246)
private def seedBody := chain [readAllowed,.cond 6 1048 acceptSeed .skip]
private def seedLoop := forCount 246 1047 64 seedBody
private lemma visitCode : src_visit=chain (makeRow++[forCount 245 1033 64 fillPoint,seedLoop]) := rfl
private def enabled (d : Instance) (cut : List ℕ) (p : ℕ) := d.active p && !cut.contains p
private lemma allowed_eq (d : Instance) (cut : List ℕ) :
    allowed d cut=(List.range d.n).filter (enabled d cut) := by
  unfold allowed vertices
  rw [List.filter_filter]
  apply List.filter_congr;intro q _
  simp [enabled,Bool.and_comm]

private lemma compose {a b c : State} (ab : Between a b) (bc : Between b c) : Between a c :=
  ⟨fun j h=>(bc.control j h).trans (ab.control j h),ab.cursor.trans bc.cursor,
    fun j h=>(bc.tables j (by have:=ab.cursor;omega)).trans (ab.tables j h),bc.count,bc.available⟩

private lemma by_program {p : Program} {n m a t k z} (old : Between z a) (run : Executes n m p a t k)
    (off : ∀j,j=6 ∨ j=7 ∨ (64 ≤ j ∧ j ≤ 82) → writesReg j p=false)
    (cur : a.reg 8 ≤ t.reg 8) (heap : ∀j < (a.reg 8).toNat,t.heap j=a.heap j)
    (out : t.output=a.output) (cl : t.closed=a.closed) : Between a t := by
  exact ⟨fun j h=>run.preserves _ (off _ (by omega)),cur,heap,
    (run.preserves _ (off 82 (.inr (.inr (by decide))))).trans
      (old.count.trans (congrArg (fun l : List Instr=>(l.length:ℤ)) out.symm)),cl.trans old.available⟩

private lemma input_kept {p : Program} {n level cut m a t k} (input : CutInput n level cut a)
    (length_ : cut.length ≤ n) (ex : Executes n m p a t k) (keep : Between a t)
    (off : ∀j,240 ≤ j → j ≤ 243 → writesReg j p=false) : CutInput n level cut t := by
  obtain ⟨b,v,bp,vp,bc,vc,bits,vec⟩:=input.rows
  have cur:=keep.cursor
  exact ⟨(ex.preserves _ (off _ (by decide) (by decide))).trans input.levelReg,
    (ex.preserves _ (off _ (by decide) (by decide))).trans input.lengthReg,
    b,v,(ex.preserves _ (off _ (by decide) (by decide))).trans bp,
    (ex.preserves _ (off _ (by decide) (by decide))).trans vp,by omega,by omega,
    fun j hj=>(keep.tables _ (by omega)).trans (bits j hj),fun j hj=>by
      exact (keep.tables _ (by omega)).trans (vec j hj)⟩

private lemma aaddr (a b : ℕ) : ((a:ℤ)+b).toNat=a+b := by omega
private lemma apos (a b : ℕ) : 0 ≤ (a:ℤ)+b := by omega

private lemma fill_one (n p active cut base : ℕ) (m : ℤ→ℤ) (s : State) (yes inCut : Bool)
    (one : s.reg 6=1) (j : s.reg 245=(p:ℤ)) (ap : s.reg 71=(active:ℤ))
    (cp : s.reg 241=(cut:ℤ)) (bp : s.reg 244=(base:ℤ))
    (ar : s.heap (active+p)=if yes then 1 else 0) (cr : s.heap (cut+p)=if inCut then 1 else 0) :
    ∃t k, Executes n m fillPoint s t k ∧ k ≤ 235 ∧
      t.heap=(if yes && !inCut then Function.update s.heap (base+p) 1 else s.heap) ∧ t.output=s.output ∧ t.closed=s.closed := by
  have raw : ∃t k,evalLine n m fillPoint s=some (t,k) ∧ k ≤ 235 ∧
      t.heap=(if yes && !inCut then Function.update s.heap (base+p) 1 else s.heap) ∧ t.output=s.output ∧ t.closed=s.closed := by
    cases yes <;> cases inCut <;> simp [fillPoint,chain,evalLine,Operation.next,regularNext,State.assign,State.save,
      one,j,ap,cp,bp,apos,aaddr,ar,cr] at ar cr ⊢
  obtain ⟨t,k,ev,c,hp⟩:=raw;exact ⟨t,k,evalLine_sound _ _ _ _ ev,c,hp⟩

private structure Mask (d : Instance) (cut : List ℕ) (s : State) : Prop where
  row : ∃b:ℕ,s.reg 244=(b:ℤ) ∧ b+d.n ≤ (s.reg 8).toNat ∧
    ∀p < d.n,s.heap (b+p)=if enabled d cut p then 1 else 0

private lemma make_allowed (d : Instance) (w level : ℕ) (cut : List ℕ) (m : ℤ→ℤ) (z a : State)
    (data : TraversalData d w z) (orig : Between z a) (args : CutInput d.n level cut a) :
    ∃t k,Executes d.n m setAllowed a t k ∧ k ≤ 400*(d.n+1) ∧ Between a t ∧ Mask d cut t ∧ t.output=a.output := by
  let base:=(a.reg 8).toNat
  have cur : a.reg 8=(base:ℤ) := by dsimp [base];have :=data.nonnegative.trans orig.cursor;omega
  have one := (orig.control 6 (.inl rfl)).trans data.one
  have zero := (orig.control 7 (.inr (.inl rfl))).trans data.zero
  have size := (orig.control 64 (.inr (.inr (by decide)))).trans data.size
  obtain ⟨active,ap,bits⟩:=data.active
  obtain ⟨cb,v,cp,_,cbound,_,cbit,_⟩:=args.rows
  have activeAt:=(orig.control 71 (.inr (.inr (by decide)))).trans ap
  have raw : ∃s k,evalLine d.n m (chain makeRow) a=some (s,k) ∧ k ≤ 72+64*d.n ∧
    s.reg 244=(base:ℤ) ∧ s.reg 8=((base+d.n:ℕ):ℤ) ∧ (∀p < d.n,s.heap (base+p)=0) ∧
    (∀j < base,s.heap j=a.heap j) ∧ s.output=a.output ∧ s.closed=a.closed := by
    simp [makeRow,chain,evalLine,Operation.next,regularNext,State.clear,State.assign,one,zero,size,cur,
      Nat.cast_add,Nat.mul_add,Nat.add_mul] <;> (repeat' apply And.intro) <;> intros <;> omega
  obtain ⟨s,k,ev,kt,bp,end_,empty,old,so,sc⟩:=raw
  have alloc:=evalLine_sound _ _ _ _ ev
  let I:=fun i (u : State) => (∀p < d.n,u.heap (base+p)=if p < i ∧ enabled d cut p=true then 1 else 0) ∧
    (∀j < base,u.heap j=a.heap j) ∧ u.output=a.output ∧ u.closed=a.closed
  obtain ⟨t,j,run,jt,done_,before,out,cl⟩:=GeometryTables.counted (n:=d.n) (m:=m) 245 1033 64 d.n 235
    fillPoint s I (by decide) (by decide) (by decide) (by decide) ((alloc.preserves 64 (by decide)).trans size)
    ⟨by simpa using empty,old,so,sc⟩ (fun _ _ _ _ _ p=>p) (by
      intro p hp u im fr idx
      obtain ⟨marks,previous,out,cl⟩:=im
      have hit := bits p hp
      have ab : active+p < base := by dsimp [base];have := orig.cursor;omega
      have ac := (previous _ ab).trans ((orig.tables _ hit.1).trans hit.2)
      have cc := (previous (cb+p) (by dsimp [base];omega)).trans (cbit p hp)
      have keep (r : ℕ) (nr : writesReg r (forCount 245 1033 64 fillPoint)=false) (na : writesReg r (chain makeRow)=false) :=
        (fr r nr).trans (alloc.preserves _ na)
      obtain ⟨v,l,ex,lt,heap,vo,vc⟩:=fill_one d.n p active cb base m u (d.active p) (cut.contains p)
        ((keep 6 (by decide) (by decide)).trans one) idx ((keep 71 (by decide) (by decide)).trans activeAt)
        ((keep 241 (by decide) (by decide)).trans cp) ((fr 244 (by decide)).trans bp) ac (by simpa using cc)
      refine ⟨v,l,ex,lt,?_,?_,vo.trans out,vc.trans cl⟩
      · intro i hi
        change v.heap (base+i)=_
        by_cases same:i=p
        · subst i
          change v.heap=(if enabled d cut p then Function.update u.heap (base+p) 1 else u.heap) at heap
          by_cases en : enabled d cut p=true <;> simp [heap,en,marks p hp]
        · have ne : base+i≠base+p := by omega
          have eq : v.heap (base+i)=u.heap (base+i) := by rw [heap];split <;> simp [Function.update_of_ne ne]
          rw [eq,marks i hi]
          by_cases earlier:i < p <;> simp [earlier,show (i < p+1) ↔ i < p by omega]
      · intro i hi
        rw [heap];split <;> simp [Function.update_of_ne (show i≠base+p by omega),previous i hi])
  obtain ⟨a₀,pre,tk⟩:=splitChain makeRow alloc
  have full : Executes d.n m setAllowed a t (a₀+(1+j+1)):=pre.continue _ (.seq run (.skip _))
  have ptr:=(run.preserves 8 (by decide)).trans end_
  refine ⟨t,_,full,by ring_nf at kt jt ⊢ <;> omega,by_program orig full ?_ (by omega) before out cl,
    ⟨base,(run.preserves 244 (by decide)).trans bp,by omega,?_⟩,out⟩
  · intro r hr
    rcases hr with rfl|rfl|⟨a,b⟩
    · decide
    · decide
    · interval_cases r <;> decide
  · intro i hi
    simpa [hi] using done_ i hi

private lemma cut_len (vs : List ℕ) (w : ℕ) (cut : List ℕ) (mem : cut∈cuts vs w) : cut.length ≤ vs.length := by
  induction vs generalizing w cut with
  | nil =>simpa [cuts] using mem
  | cons v vs ih =>
    cases w with
    | zero =>simp [cuts] at mem;subst cut;simp
    | succ w =>
      simp only [cuts,List.mem_append,List.mem_map] at mem
      rcases mem with small | ⟨c,h,rfl⟩
      · have := ih _ _ small;simp;omega
      · simp;exact ih _ _ h

private lemma form_piece (d : Instance) (cut : List ℕ) (seed : ℕ) (pos : 0 < d.n) :
    ∃f:ℕ→Bool, pieceAt d (allowed d cut) seed=(List.range d.n).filter f := by
  have hs : List.range d.n=List.range (d.n-1)++[d.n-1] := by rw [←List.range_succ];congr 1;omega
  unfold pieceAt
  rw [hs,List.foldl_append,List.foldl_cons,List.foldl_nil,allowed_eq,List.filter_filter,←hs]
  exact ⟨_,rfl⟩

private lemma read_points (d : Instance) (cut : List ℕ) (seed base : ℕ) (s : State)
    (pos : 0 < d.n) (row : ∀p < d.n,s.heap (base+p)=if p∈pieceAt d (allowed d cut) seed then 1 else 0) :
    (List.range d.n).filter (fun j=>decide (1 ≤ s.heap (base+j)))=pieceAt d (allowed d cut) seed := by
  obtain ⟨f,im⟩:=form_piece d cut seed pos
  rw [im];apply List.filter_congr
  intro p hp
  have b:=row p (List.mem_range.mp hp)
  rw [im] at b
  cases hf:f p <;> simp [b,hp,hf]

private lemma testa (n i j : ℕ) (m : ℤ→ℤ) (s : State) (ri:s.reg 147=(i:ℤ)) (rj:s.reg 246=(j:ℤ)) :
    ∃t k,Executes n m (chain testHead) s t k ∧ k ≤ 10 ∧ t.reg 1054=(if i=j then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  have raw : ∃t k,evalLine n m (chain testHead) s=some (t,k) ∧ k ≤ 10 ∧ t.reg 1054=(if i=j then 1 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    by_cases h : i ≤ j <;> by_cases l : j ≤ i <;> by_cases e : i=j <;> (try omega) <;>
      simp [testHead,chain,evalLine,Operation.next,regularNext,State.assign,ri,rj,h,l,e]
  obtain ⟨t,k,ev,kt,res⟩:=raw;exact ⟨t,k,evalLine_sound _ _ _ _ ev,kt,res⟩

private lemma scan_seed (d : Instance) (w level seed : ℕ) (cut : List ℕ) (m : ℤ→ℤ) (z s : State)
    (data : TraversalData d w z) (edge : ∃g:ℕ,z.reg 75=(g:ℤ) ∧ ∀q < d.n,∀p < d.n,
      g+(q*d.n+p)<(z.reg 8).toNat ∧ z.heap (g+(q*d.n+p))=if d.edge q p then 1 else 0)
    (sz : seed < d.n) (yes : enabled d cut seed=true) (im : Mask d cut s) (hs : Between z s)
    (input : CutInput d.n level cut s) (idx : s.reg 246=(seed:ℤ)) :
    let c:=pieceAt d (allowed d cut) seed
    ∃t k, Executes d.n m readComponent s t k ∧ k ≤ 1050*(d.n+1)^4 ∧
      Between s t ∧ t.reg 1054=(if c.head?=some seed then 1 else 0) ∧
      ComponentArg d.n c t ∧ t.output=s.output := by
  classical
  let c:=pieceAt d (allowed d cut) seed
  let base:=(s.reg 8).toNat
  obtain ⟨a,ap,lim,bits⟩:=im.row
  obtain ⟨g,gp,edges⟩:=edge
  have nonneg:=data.nonnegative.trans hs.cursor
  have cur:s.reg 8=(base:ℤ):=by dsimp [base];omega
  have one := (hs.control 6 (.inl rfl)).trans data.one
  have zero := (hs.control 7 (.inr (.inl rfl))).trans data.zero
  have size := (hs.control 64 (.inr (.inr (by decide)))).trans data.size
  let a':=(s.assign 132 (s.reg 244)).assign 133 (s.reg 246)
  have setup : Executes d.n m (chain setSeed) s a' 5 := evalLine_sound _ _ _ _ rfl
  obtain ⟨b,k,run,kt,ptr,next,members,old,ob,cb⟩:=Scene.ComponentScan.connected_component_bitmap d
    (enabled d cut) base a g seed m a' sz yes one zero size cur
    (by simpa [a',State.assign] using idx) (by simpa [a',State.assign] using ap)
    ((hs.control 75 (.inr (.inr (by decide)))).trans gp)
    (by intro p hp;dsimp [base];omega) bits
    (by intro q hq p hp;have := (edges q hq p hp).1;have := hs.cursor;dsimp [base];omega)
    (fun q hq p hp=>(hs.tables _ (edges q hq p hp).1).trans (edges q hq p hp).2)
  have row : ∀j < d.n,b.heap (base+j)=if j∈c then 1 else 0 := by simpa [c,allowed_eq] using members
  let v:=((b.assign 1051 (b.reg 138)).assign 247 (b.reg 138)).assign 144 (b.reg 138)
  have set : Executes d.n m (chain setFirst) b v 7 := evalLine_sound _ _ _ _
    (by simp [setFirst,chain,evalLine,Operation.next,regularNext,State.assign,v])
  obtain ⟨u,j,first,jt,read,hv,ov,cv⟩:=matrix_and_row_scans.2.1 d.n base m v
    ((set.preserves _ (by decide)).trans ((run.preserves _ (by decide)).trans one))
    ((set.preserves _ (by decide)).trans ((run.preserves _ (by decide)).trans size))
    (by simpa [v,State.assign] using ptr)
  have heq : u.reg 147=(c.headD d.n:ℤ) := by
    dsimp only [c]
    rw [←read_points d cut seed base v (by omega) row];exact read
  obtain ⟨t,l,test,lt,flag,hu,ot,ct⟩:=testa d.n (c.headD d.n) seed m u heq
    ((first.preserves _ (by decide)).trans ((set.preserves _ (by decide)).trans ((run.preserves _ (by decide)).trans idx)))
  obtain ⟨i,pi,tmi⟩:=splitChain setSeed setup
  obtain ⟨a₀,pa,ta⟩:=splitChain setFirst set
  have full : Executes d.n m readComponent s t (i+(1+k+(a₀+(1+j+l)))) :=
    pi.continue _ (.seq run (pa.continue _ (.seq first test)))
  have last8 : t.reg 8=((base+d.n:ℕ):ℤ) := (test.preserves _ (by decide)).trans
    ((first.preserves _ (by decide)).trans ((set.preserves _ (by decide)).trans next))
  have cells : t.heap=b.heap := hu.trans hv
  have out : t.output=s.output := ot.trans (ov.trans ob)
  have close : t.closed=s.closed := ct.trans (cv.trans cb)
  have head : c.headD d.n=seed ↔ c.head?=some seed := by cases c <;> simp <;> omega
  refine ⟨t,_,full,by ring_nf at kt jt lt ⊢ <;> omega,by_program hs full ?_ (by omega)
    (fun j hj=>(congrFun cells _).trans (old j (.inl hj))) out close,by simpa only [head] using flag,
    ⟨base,(test.preserves _ (by decide)).trans ((first.preserves _ (by decide)).trans (by simpa [v,State.assign] using ptr)),
      by omega,fun j hj=>(congrFun cells _).trans (row j hj)⟩,out⟩
  intro x hx;rcases hx with rfl|rfl|⟨le,le'⟩
  · decide
  · decide
  · interval_cases x <;> decide

private def emitSeed (d : Instance) (level : ℕ) (cut : List ℕ) (p : ℕ) :=
  let c:=pieceAt d (allowed d cut) p
  if enabled d cut p && (c.head?==some p) then visitTape Naming.name d level cut c else []

private lemma emission (d : Instance) (level : ℕ) (cut : List ℕ) :
    (List.range d.n).flatMap (emitSeed d level cut)=cutTape d level cut := by
  change _=((allowed d cut).filterMap (fun p=>let c:=pieceAt d (allowed d cut) p
    if c.head?==some p then some c else none)).flatMap (visitTape Naming.name d level cut)
  conv_rhs => arg 2;arg 2;rw [allowed_eq]
  generalize List.range d.n=xs
  induction xs with
  | nil =>rfl
  | cons p ps ih =>
    by_cases live : enabled d cut p=true <;> by_cases head : (pieceAt d (allowed d cut) p).head?=some p <;>
      simp [emitSeed,live,head,ih]

private lemma handle_seed (d : Instance) (w level V seed : ℕ) (cut : List ℕ) (m : ℤ→ℤ) (z s : State)
    (data : TraversalData d w z) (edge : ∃g:ℕ,z.reg 75=(g:ℤ) ∧ ∀q < d.n,∀p < d.n,
      g+(q*d.n+p) < (z.reg 8).toNat ∧ z.heap (g+(q*d.n+p))=if d.edge q p then 1 else 0)
    (reps : Representatives d w level m z V) (valid : cut∈cuts (vertices d) (min w d.n))
    (length_ : cut.length ≤ d.n) (sz : seed < d.n) (im : Mask d cut s) (hs : Between z s)
    (input : CutInput d.n level cut s) (idx : s.reg 246=(seed:ℤ)) :
    ∃t k,Executes d.n m seedBody s t k ∧ k ≤ 1200*(d.n+1)^4+V ∧
      Between s t ∧ t.output=s.output++emitSeed d level cut seed := by
  classical
  obtain ⟨b,ptr,lim,cell⟩:=im.row
  let a:=s.assign 1048 (s.heap (b+seed))
  have fetch : Executes d.n m readAllowed s a 64 := by
    apply evalLine_sound
    simp [readAllowed,evalLine,Operation.next,a,State.assign,ptr,idx,apos,aaddr]
  have sa : Between s a := by
    apply by_program hs fetch _ le_rfl (fun _ _=>rfl) rfl rfl
    intro r hr;simp [readAllowed,writesReg,writesOp];omega
  have inside:=input_kept input length_ fetch sa (by intro r h h';simp [readAllowed,writesReg,writesOp];omega)
  have mask : Mask d cut a := ⟨b,ptr,lim,cell⟩
  have one : a.reg 6=1 := (hs.control 6 (.inl rfl)).trans data.one
  have bit : a.reg 1048=(if enabled d cut seed then 1 else 0) := by simpa [a,State.assign] using cell seed sz
  have charge : 1 ≤ (d.n+1)^4 := Nat.one_le_pow _ _ (by omega)
  by_cases yes : enabled d cut seed=true
  · have enter : a.reg 6 ≤ a.reg 1048 := by rw [one,bit,if_pos yes]
    let c:=pieceAt d (allowed d cut) seed
    obtain ⟨u,k,scan,kt,au,flag,row,out⟩:=scan_seed d w level seed cut m z a data edge sz yes mask (compose hs sa) inside idx
    have unit:=(au.control 6 (.inl rfl)).trans one
    have cu:=input_kept inside length_ scan au (by intro j h h';interval_cases j <;> decide)
    obtain ⟨j,pre,kj⟩:=splitChain (setSeed++[src_component]++setFirst++[src_first]++testHead) scan
    by_cases head : c.head?=some seed
    · have allowedSeed : seed∈allowed d cut := by rw [allowed_eq];simp [sz,yes]
      obtain ⟨v,l,body,lt,uv,vo⟩:=reps u cut seed (compose (compose hs sa) au) valid cu allowedSeed
        ((scan.preserves 246 (by decide)).trans idx) head row
      have ok : u.reg 6 ≤ u.reg 1054 := by rw [unit,flag,if_pos head]
      have path : Executes d.n m acceptSeed a v (j+(1+(1+l)+1)):=pre.continue _ (.seq (.yes ok body) (.skip _))
      refine ⟨v,_,.seq fetch (.seq (.yes enter path) (.skip _)),by omega,compose (compose sa au) uv,?_⟩
      simpa [emitSeed,yes,show (pieceAt d (allowed d cut) seed).head?=some seed from head,out,a,State.assign] using vo
    · have fail : ¬u.reg 6 ≤ u.reg 1054 := by rw [unit,flag,if_neg head];decide
      have path : Executes d.n m acceptSeed a u (j+(1+(1+1)+1)):=pre.continue _ (.seq (.no fail (.skip _)) (.skip _))
      refine ⟨u,_,.seq fetch (.seq (.yes enter path) (.skip _)),by omega,compose sa au,?_⟩
      simpa [emitSeed,yes,show (pieceAt d (allowed d cut) seed).head?≠some seed from head,a,State.assign] using out
  · have no : ¬a.reg 6 ≤ a.reg 1048 := by rw [one,bit,if_neg yes];decide
    refine ⟨a,_,.seq fetch (.seq (.no no (.skip _)) (.skip _)),by omega,sa,?_⟩
    simp [a,State.assign,emitSeed,yes]

private lemma between_assign {s t : State} (given : Between s t) (r : ℕ) (hi : 82 < r) (v : ℤ) :
    Between s (t.assign r v) := by
  refine ⟨?_,?_,given.tables,?_,given.available⟩
  · intro j hj
    simpa [State.assign,show j≠r by omega] using given.control j hj
  · simpa [State.assign,show 8≠r by omega] using given.cursor
  · simpa [State.assign,show 82≠r by omega] using given.count

private lemma visit_program (d : Instance) (w level V : ℕ) (m : ℤ→ℤ) (z : State)
    (data : TraversalData d w z) (edge : ∃g:ℕ,z.reg 75=(g:ℤ) ∧ ∀q < d.n,∀p < d.n,
      g+(q*d.n+p) < (z.reg 8).toNat ∧ z.heap (g+(q*d.n+p))=if d.edge q p then 1 else 0)
    (reps : Representatives d w level m z V) :
    Visits d w level m z (2000*(V+1)*(d.n+1)^5) := by
  intro a cut ha valid input
  have length_ := (cut_len _ _ _ valid).trans (show (vertices d).length ≤ d.n by
    simpa [vertices] using List.length_filter_le d.active (List.range d.n))
  obtain ⟨s,k,build,kt,as_,ms,out⟩:=make_allowed d w level cut m z a data ha input
  have zs:=compose ha as_
  have size:=(zs.control 64 (.inr (.inr (by decide)))).trans data.size
  have inside:=input_kept input length_ build as_ (by intro j lo hi;interval_cases j <;> decide)
  let I:=fun i (u : State) => Between s u ∧ u.output=s.output++(List.range i).flatMap (emitSeed d level cut)
  have rng : Between s s := ⟨fun _ _=>rfl,le_rfl,fun _ _=>rfl,as_.count,as_.available⟩
  obtain ⟨t,j,run,jt,st,output⟩:=GeometryTables.counted (n:=d.n) (m:=m) 246 1047 64 d.n (1200*(d.n+1)^4+V)
    seedBody s I (by decide) (by decide) (by decide) (by decide) size ⟨rng,by simp⟩ (by
      intro i u r v which pr
      rcases which with rfl|rfl <;> exact ⟨between_assign pr.1 _ (by decide) _,pr.2⟩) (by
      intro i hi u pr fr ix
      obtain ⟨su,uo⟩:=pr
      have cm : CutInput d.n level cut u := by
        obtain ⟨b,v,bp,vp,bc,vc,bits,vec⟩:=inside.rows
        have cur:=su.cursor
        exact ⟨(fr 240 (by decide)).trans inside.levelReg,(fr 243 (by decide)).trans inside.lengthReg,
          b,v,(fr 241 (by decide)).trans bp,(fr 242 (by decide)).trans vp,by omega,by omega,
          fun h hh=>(su.tables _ (by omega)).trans (bits h hh),
          fun h hh=>(su.tables _ (by omega)).trans (vec h hh)⟩
      have mask : Mask d cut u := by
        obtain ⟨b,ptr,bc,bits⟩:=ms.row
        exact ⟨b,(fr 244 (by decide)).trans ptr,by have:=su.cursor;omega,
          fun p hp=>(su.tables _ (by omega)).trans (bits p hp)⟩
      obtain ⟨v,l,ex,lt,uv,vo⟩:=handle_seed d w level V i cut m z u data edge reps valid length_ hi mask
        (compose zs su) cm ix
      exact ⟨v,l,ex,lt,compose su uv,by simp [vo,uo,List.range_succ,List.append_assoc]⟩)
  obtain ⟨i,pre,ki⟩:=splitChain (makeRow++[forCount 245 1033 64 fillPoint]) build
  rw [visitCode]
  refine ⟨t,_,pre.continue _ (.seq run (.skip _)),by ring_nf at kt jt ⊢ <;> omega,compose as_ st,?_⟩
  simpa [out,emission] using output
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


private lemma edge_scene (x : World) (s : Store) (r h w : ℕ) (u v z : State)
    (prep : Prepared x.n r h w u) (geo : Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h u v)
    (menus : Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h v z) :
    let d:=integerData x.n x.mem s.imem r h
    ∃g:ℕ,z.reg 75=(g:ℤ) ∧ ∀q < d.n,∀p < d.n,g+(q*d.n+p) < (z.reg 8).toNat ∧
      z.heap (g+(q*d.n+p))=if d.edge q p then 1 else 0 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,atRegs,_,_,_⟩:=prep
  let o:=offsets x.n (sizes x.n h)
  refine ⟨cursorAt o 4,(menus.controls 75 (.inr (.inr (by decide)))).trans
    ((geo.controls 75 (.inr (.inr (.inr (by decide))))).trans (atRegs ⟨4,by decide⟩)),?_⟩
  intro q hq p hp
  change q < x.n at hq;change p < x.n at hp
  have upper:=Nat.mul_le_mul_right x.n (Nat.succ_le_of_lt hq)
  rw [Nat.succ_mul] at upper
  have inside : cursorAt o 4+(q*x.n+p) < cursorAt o 5 := by simp [o,cursorAt,offsets];omega
  have high : cursorAt o 5 ≤ cursorAt o 11 := by simp [o,cursorAt,offsets] <;> omega
  have cur:=menus.cursor
  change _ ∧ z.heap (cursorAt o 4+(q*x.n+p))=_
  refine ⟨by change cursorAt o 4+(q*x.n+p) < _;change (cursorAt o 11:ℤ) ≤ z.reg 8 at cur;omega,?_⟩
  rw [menus.geometry _ inside]
  simpa [integerData,arrange,Bits.normalized,Bits.lookup,hp,hq,o] using geo.edge ⟨q,hq⟩ ⟨p,hp⟩

lemma from_representatives (rep :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀level<x.n, let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      Scene.CutTraversal.Representatives d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)))) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀level<x.n, let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      Scene.CutTraversal.Visits d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ))) := by
  obtain ⟨c,D,b,per⟩:=rep
  refine ⟨2000*(c+1),D+5,b,?_⟩
  intro e ep e1 x s low high ready bounded r p rp pp bound key u prep v geo z menus level hl
  let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
  let w:=widthBound (e:ℝ)
  let E:=parameterEnvelope (e:ℝ)
  let V:=c*x.cap^D*x.n^(b*E)
  have each:=per e ep e1 x s low high ready bounded r p rp pp bound key u prep v geo z menus level hl
  have all_:=visit_program d w level V s.imem z (from_scene x s r _ w u v z prep geo menus)
    (edge_scene x s r _ w u v z prep geo menus) each
  change Visits d w level s.imem z (2000*(c+1)*x.cap^(D+5)*x.n^(b*E))
  intro a cut ha valid input
  obtain ⟨t,k,ex,kt,fr,ot⟩:=all_ a cut ha valid input
  refine ⟨t,k,ex,kt.trans ?_,fr,ot⟩
  have nc : x.n+1 ≤ x.cap := by dsimp [World.cap];omega
  have unit : 1 ≤ x.cap^D*x.n^(b*E) := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  have up : V+1 ≤ (c+1)*x.cap^D*x.n^(b*E) := by dsimp [V];rw [Nat.add_mul,Nat.add_mul,one_mul];omega
  change 2000*(V+1)*(x.n+1)^5 ≤ 2000*(c+1)*x.cap^(D+5)*x.n^(b*E)
  calc
    _ ≤ 2000*((c+1)*x.cap^D*x.n^(b*E))*x.cap^5 := Nat.mul_le_mul (Nat.mul_le_mul_left _ up) (Nat.pow_le_pow_left nc 5)
    _ = _ := by rw [pow_add];ring

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal

theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀level<x.n, let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      Scene.CutTraversal.Visits d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ))) := Scene.CutTraversal.from_representatives Logical.Root.write_component_representative
