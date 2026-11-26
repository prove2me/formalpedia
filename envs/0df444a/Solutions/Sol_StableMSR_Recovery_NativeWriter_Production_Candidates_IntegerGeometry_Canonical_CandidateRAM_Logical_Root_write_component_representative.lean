-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.write_component_representative
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T12:46:35.912403+00:00
-- url     : https://prove2.me/submissions/c8dbed4c-e69f-44c0-9c34-d972b127c6d2

import Definitions.Def_StableMSR_EligibleSeparatorRows
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_SeparatorRows_component_rim_bitmap
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_matrix_and_row_scans
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_write_eligible_component_entries
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


private def clearSum : List Program := [.op (.regular (.set 1058 0)),.op (.regular (.copy 248 1058))]
private def addBit := chain [.op (.fetch 1063 247 245),.op (.regular (.add 1061 248 1063)),.op (.regular (.copy 248 1061))]
private def matchSize : List Program := [.op (.regular (.set 1071 1)),.op (.regular (.add 1069 240 1071)),
  .cond 248 1069 (.cond 1069 248 (.op (.regular (.set 1067 1))) (.op (.regular (.set 1067 0))))
    (.op (.regular (.set 1067 0))),.op (.regular (.copy 1066 1067))]
private def sizeList := clearSum++[forCount 245 1060 64 addBit]++matchSize
private def prepRim : List Program := [.op (.regular (.copy 139 247))]
private def prepCompare : List Program := [.op (.regular (.copy 1073 143)),.op (.regular (.copy 148 1073)),
  .op (.regular (.copy 149 241))]
private def returnCompare : List Program := [.op (.regular (.copy 1072 152)),.op (.regular (.copy 1066 1072))]
private def checkRim := chain (prepRim++[src_rim]++prepCompare++[src_equal_rows]++returnCompare)
private lemma repCode : representativeWork=chain (sizeList++[.cond 6 1066 checkRim .skip,.cond 6 1066 entryProgram .skip]) := rfl

private lemma cut_sublist (vs : List ℕ) (w : ℕ) (cut : List ℕ) (mem : cut∈cuts vs w) : cut.Sublist vs := by
  induction vs generalizing w cut with
  | nil =>simp [cuts] at mem;subst cut;exact .slnil
  | cons v vs ih =>
    cases w with
    | zero =>simp [cuts] at mem;subst cut;exact List.nil_sublist _
    | succ w =>
      simp only [cuts,List.mem_append,List.mem_map] at mem
      rcases mem with h|⟨b,h,rfl⟩
      · exact (ih _ _ h).cons v
      · exact (ih _ _ h).cons_cons v

private lemma recover_filter {xs ys : List ℕ} (sub : xs.Sublist ys) (nd : ys.Nodup) :
    ys.filter (fun q=>decide (q∈xs))=xs := by
  induction sub with
  | slnil =>rfl
  | @cons xs ys a sub ih =>
    obtain ⟨out,tail⟩:=List.nodup_cons.mp nd
    have no : a∉xs := fun h=>out (sub.subset h)
    simp [no,ih tail]
  | @cons_cons xs ys a sub ih =>
    obtain ⟨out,tail⟩:=List.nodup_cons.mp nd
    have f : ys.filter (fun q=>decide (q∈a::xs))=ys.filter (fun q=>decide (q∈xs)) := by
      apply List.filter_congr
      intro q hq
      have ne : q≠a := by rintro rfl;exact out hq
      simp [ne]
    rw [List.filter_cons_of_pos (by simp),f,ih tail]

private lemma count_bits (d : Instance) (level seed : ℕ) (cut : List ℕ) (m : ℤ→ℤ) (s : State)
    (pos : 0 < d.n) (sz : s.reg 64=(d.n:ℤ)) (lev : s.reg 240=(level:ℤ))
    (arg : ComponentArg d.n (pieceAt d (allowed d cut) seed) s) :
    let c:=pieceAt d (allowed d cut) seed
    ∃t k,Executes d.n m (chain sizeList) s t k ∧ k ≤ 140*(d.n+1) ∧
      t.reg 1066=(if c.length=level+1 then 1 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  classical
  let c:=pieceAt d (allowed d cut) seed
  obtain ⟨b,base,_,bits⟩:=arg.row
  let seenBits:=fun i=>(List.range i).filter (fun j=>decide (j∈c))
  let a:=(s.assign 1058 0).assign 248 0
  have init : Executes d.n m (chain clearSum) s a 5 := evalLine_sound _ _ _ _ rfl
  let I:=fun i (u : State) => u.reg 248=((seenBits i).length:ℤ) ∧ u.heap=s.heap ∧ u.output=s.output ∧ u.closed=s.closed
  obtain ⟨u,k,loop,kt,res,heap,out,cl⟩:=GeometryTables.counted (n:=d.n) (m:=m) 245 1060 64 d.n 75 addBit a I
    (by decide) (by decide) (by decide) (by decide) ((init.preserves _ (by decide)).trans sz)
    ⟨by simp [a,seenBits,State.assign],rfl,rfl,rfl⟩ (by
      intro j t r v which ok;rcases which with rfl|rfl <;> exact ⟨by simpa [State.assign] using ok.1,ok.2⟩) (by
      intro i hi t im fr idx
      obtain ⟨cnt,mem,ot,ct⟩:=im
      have ptr:=(fr 247 (by decide)).trans ((init.preserves 247 (by decide)).trans base)
      have mark: t.heap (b+i)=if i∈c then 1 else 0 := (congrFun mem _).trans (bits i hi)
      have raw : ∃t' j,evalLine d.n m addBit t=some (t',j) ∧ j ≤ 75 ∧ I (i+1) t' := by
        by_cases yes:i∈c <;>
          simp [addBit,chain,evalLine,Operation.next,regularNext,State.assign,ptr,idx,apos,aaddr,mark,yes,I,cnt,
            seenBits,List.range_succ,List.filter_append,mem,ot,ct]
      obtain ⟨v,j,ev,jt,h⟩:=raw;exact ⟨v,j,evalLine_sound _ _ _ _ ev,jt,h⟩)
  have equals : seenBits d.n=c := by
    obtain ⟨f,h⟩:=form_piece d cut seed pos
    apply recover_filter _ List.nodup_range
    dsimp [c];rw [h];exact List.filter_sublist
  have sum : u.reg 248=(c.length:ℤ) := by simpa [equals] using res
  have target:=(loop.preserves 240 (by decide)).trans ((init.preserves 240 (by decide)).trans lev)
  have raw : ∃v j,evalLine d.n m (chain matchSize) u=some (v,j) ∧ j ≤ 12 ∧
      v.reg 1066=(if c.length=level+1 then 1 else 0) ∧ v.heap=u.heap ∧ v.output=u.output ∧ v.closed=u.closed := by
    have le₁ : ((c.length:ℤ) ≤ (level:ℤ)+1) ↔ c.length ≤ level+1 := by omega
    have le₂ : ((level:ℤ)+1 ≤ c.length) ↔ level+1 ≤ c.length := by omega
    by_cases h : c.length ≤ level+1 <;> by_cases l : level+1 ≤ c.length <;> by_cases e:c.length=level+1 <;>
      (try omega) <;> simp [matchSize,chain,evalLine,Operation.next,regularNext,State.assign,sum,target,le₁,le₂,h,l,e]
  obtain ⟨v,j,ev,jt,ans,hv,ov,cv⟩:=raw
  obtain ⟨i,pre,tm⟩:=splitChain clearSum init
  exact ⟨v,_,pre.continue _ (.seq loop (evalLine_sound _ _ _ _ ev)),by omega,ans,hv.trans heap,ov.trans out,cv.trans cl⟩

private lemma rim_bits (d : Instance) (c : List ℕ) (p : ℕ) (hp : p < d.n) (bound : ∀q∈c,q < d.n) :
    p∈rimOf d c ↔ d.active p=true ∧ p∉c ∧ ∃q < d.n,q∈c ∧ d.edge q p=true := by
  simp only [rimOf,vertices,List.mem_filter,List.mem_range,hp,true_and,Bool.and_eq_true,
    Bool.not_eq_true',List.any_eq_true]
  constructor
  · rintro ⟨on,abs,q,hq,edge⟩;exact ⟨on,by simpa using abs,q,bound q hq,hq,edge⟩
  · rintro ⟨on,abs,q,_,hq,edge⟩;exact ⟨on,by simpa using abs,q,hq,edge⟩

private lemma check_boundary (d : Instance) (w level seed : ℕ) (cut : List ℕ) (m : ℤ→ℤ) (z s : State)
    (data : TraversalData d w z) (edge : ∃g:ℕ,z.reg 75=(g:ℤ) ∧ ∀q < d.n,∀p < d.n,
      g+(q*d.n+p) < (z.reg 8).toNat ∧ z.heap (g+(q*d.n+p))=if d.edge q p then 1 else 0)
    (pos : 0 < d.n) (cutOk : cut∈cuts (vertices d) (min w d.n)) (hs : Between z s) (input : CutInput d.n level cut s)
    (arg : ComponentArg d.n (pieceAt d (allowed d cut) seed) s) :
    let c:=pieceAt d (allowed d cut) seed
    ∃t k,Executes d.n m checkRim s t k ∧ k ≤ 1000*(d.n+1)^3 ∧
      Between s t ∧ t.reg 1066=(if rimOf d c=cut then 1 else 0) ∧ t.output=s.output := by
  classical
  let c:=pieceAt d (allowed d cut) seed
  let cursor:=(s.reg 8).toNat
  have cur : s.reg 8=(cursor:ℤ) := by dsimp [cursor];have := data.nonnegative.trans hs.cursor;omega
  obtain ⟨a,whereA,active⟩:=data.active
  obtain ⟨g,whereG,edges⟩:=edge
  obtain ⟨b,ptr,lim,bits⟩:=arg.row
  obtain ⟨cb,cv,cutAt,_,cutBelow,_,cutBits,_⟩:=input.rows
  have one := (hs.control 6 (.inl rfl)).trans data.one
  have zero := (hs.control 7 (.inr (.inl rfl))).trans data.zero
  have sz := (hs.control 64 (.inr (.inr (by decide)))).trans data.size
  let u:=s.assign 139 (s.reg 247)
  have prepare : Executes d.n m (chain prepRim) s u 3 := evalLine_sound _ _ _ _ rfl
  obtain ⟨v,k,run,kt,ans,next,row,frame,out,cl⟩:=Scene.SeparatorRows.component_rim_bitmap d.n cursor a b g m u
    d.active (fun q=>decide (q∈c)) d.edge one zero sz cur ((hs.control 71 (.inr (.inr (by decide)))).trans whereA)
    (by simpa [u,State.assign] using ptr) ((hs.control 75 (.inr (.inr (by decide)))).trans whereG)
    (fun p hp=>(hs.tables _ (active p hp).1).trans (active p hp).2)
    (by intro q hq;simpa [u,State.assign,c] using bits q hq)
    (fun q hq p hp=>(hs.tables _ (edges q hq p hp).1).trans (edges q hq p hp).2)
    (by intro q hq;have := (active q hq).1;have := hs.cursor;dsimp [cursor];omega)
    (by intro q hq p hp;have := (edges q hq p hp).1;have := hs.cursor;dsimp [cursor];omega)
  obtain ⟨f,form⟩:=form_piece d cut seed pos
  have cbound : ∀q∈c,q < d.n := by simpa [c,form] using
    (show ∀q∈(List.range d.n).filter f,q < d.n from fun q h=>List.mem_range.mp (List.mem_filter.mp h).1)
  have bitmap (p : ℕ) (hp:p < d.n) : v.heap (cursor+p)=if p∈rimOf d c then 1 else 0 := by
    simpa [rim_bits d c p hp cbound] using row p hp
  have bv : v.reg 241=(cb:ℤ) := (run.preserves _ (by decide)).trans cutAt
  let a':=((v.assign 1073 (v.reg 143)).assign 148 (v.reg 143)).assign 149 (v.reg 241)
  have args : Executes d.n m (chain prepCompare) v a' 7 := evalLine_sound _ _ _ _
    (by simp [prepCompare,chain,evalLine,Operation.next,regularNext,State.assign,a'])
  obtain ⟨y,j,equal,jt,ones,binary,hy,oy,cy⟩:=matrix_and_row_scans.2.2 d.n cursor cb m a'
    ((args.preserves _ (by decide)).trans ((run.preserves _ (by decide)).trans one))
    ((args.preserves _ (by decide)).trans ((run.preserves _ (by decide)).trans sz))
    (by simpa [a',State.assign] using ans) (by simpa [a',State.assign] using bv)
  have canonicalCut : (List.range d.n).filter (fun p=>decide (p∈cut))=cut :=
    recover_filter ((cut_sublist _ _ _ cutOk).trans List.filter_sublist) List.nodup_range
  have canonicalRim : (List.range d.n).filter (fun p=>decide (p∈rimOf d c))=rimOf d c :=
    recover_filter (List.filter_sublist.trans (show (vertices d).Sublist (List.range d.n) from List.filter_sublist)) List.nodup_range
  have iff : y.reg 152=1 ↔ rimOf d c=cut := by
    rw [ones]
    have right (p : ℕ) (hp:p < d.n) : a'.heap (cb+p)=if p∈cut then 1 else 0 :=
      (frame _ (.inl (by dsimp [cursor];omega))).trans (cutBits p hp)
    constructor
    · intro eq
      rw [←canonicalRim,←canonicalCut]
      apply List.filter_congr
      intro p hp
      have h:=List.mem_range.mp hp
      have left : a'.heap (cursor+p)=if p∈rimOf d c then 1 else 0 := bitmap p h
      have e:=eq p h
      rw [left,right p h] at e
      by_cases l:p∈rimOf d c <;> by_cases r:p∈cut <;> simp_all
    · intro eq p hp
      change v.heap (cursor+p)=_
      rw [bitmap p hp,eq,right p hp]
  let t:=(y.assign 1072 (y.reg 152)).assign 1066 (y.reg 152)
  have final_ : Executes d.n m (chain returnCompare) y t 5 := evalLine_sound _ _ _ _
    (by simp [returnCompare,chain,evalLine,Operation.next,regularNext,State.assign,t])
  obtain ⟨i,pre,pi⟩:=splitChain prepRim prepare
  obtain ⟨l,mid,ml⟩:=splitChain prepCompare args
  have full : Executes d.n m checkRim s t (i+(1+k+(l+(1+j+5)))) :=
    pre.continue _ (.seq run (mid.continue _ (.seq equal final_)))
  have last8 : t.reg 8=((cursor+d.n:ℕ):ℤ) := (final_.preserves _ (by decide)).trans
    ((equal.preserves _ (by decide)).trans ((args.preserves _ (by decide)).trans next))
  have output : t.output=s.output := oy.trans out
  refine ⟨t,_,full,by ring_nf at kt jt ⊢ <;> omega,by_program hs full ?_ (by omega)
    (fun j hj=>(congrFun hy _).trans (frame j (.inl hj))) output (cy.trans cl),?_,output⟩
  · intro r hr;rcases hr with rfl|rfl|⟨a,b⟩
    · decide
    · decide
    · interval_cases r <;> decide
  · change y.reg 152=_
    by_cases ok:rimOf d c=cut
    · exact (iff.mpr ok).trans (if_pos ok).symm
    · exact (binary.resolve_right (mt iff.mp ok)).trans (if_neg ok).symm

private lemma component_kept {n c m a t k} {p : Program} (src : ComponentArg n c a)
    (ex : Executes n m p a t k) (bt : Between a t) (off : writesReg 247 p=false) : ComponentArg n c t := by
  obtain ⟨b,ptr,lim,row⟩:=src.row
  exact ⟨b,(ex.preserves _ off).trans ptr,by have:=bt.cursor;omega,
    fun j hj=>(bt.tables _ (by omega)).trans (row j hj)⟩

private lemma representative_program (d : Instance) (w level V : ℕ) (m : ℤ→ℤ) (z : State)
    (data : TraversalData d w z) (edge : ∃g:ℕ,z.reg 75=(g:ℤ) ∧ ∀q < d.n,∀p < d.n,
      g+(q*d.n+p) < (z.reg 8).toNat ∧ z.heap (g+(q*d.n+p))=if d.edge q p then 1 else 0)
    (entries : Entries d w level m z V) : Representatives d w level m z (2000*(V+1)*(d.n+1)^3) := by
  intro s cut seed hs valid input seedIn idx
  let c:=pieceAt d (allowed d cut) seed
  change c.head?=some seed → ComponentArg d.n c s → _
  intro head row
  have pos : 0 < d.n := by
    rw [allowed_eq,List.mem_filter,List.mem_range] at seedIn;omega
  have len := (cut_len _ _ _ valid).trans (show (vertices d).length ≤ d.n by
    simpa [vertices] using List.length_filter_le d.active (List.range d.n))
  have size := (hs.control 64 (.inr (.inr (by decide)))).trans data.size
  obtain ⟨a,k,count,kt,flag,heap,out,cl⟩:=count_bits d level seed cut m s pos size input.levelReg row
  have sa : Between s a := by
    refine by_program hs count ?_ (le_of_eq (count.preserves 8 (by decide)).symm)
      (fun j _=>congrFun heap j) out cl
    intro r hr;rcases hr with rfl|rfl|⟨lo,hi⟩
    · decide
    · decide
    · interval_cases r <;> decide
  have za:=compose hs sa
  have one:=(za.control 6 (.inl rfl)).trans data.one
  have cutA:=input_kept input len count sa (by intro j lo hi;interval_cases j <;> decide)
  have rowA:=component_kept row count sa (by decide)
  let test:=Program.cond 6 1066 checkRim .skip
  have checked : ∃b j,Executes d.n m test a b j ∧ j ≤ 1+1000*(d.n+1)^3 ∧ Between a b ∧
      b.reg 1066=(if c.length=level+1 ∧ rimOf d c=cut then 1 else 0) ∧ b.output=a.output := by
    by_cases rightSize:c.length=level+1
    · have ok : a.reg 6 ≤ a.reg 1066 := by rw [one,flag,if_pos rightSize]
      obtain ⟨b,j,ex,jt,ab,fresh,ob⟩:=check_boundary d w level seed cut m z a data edge pos valid za cutA rowA
      exact ⟨b,_,.yes ok ex,by omega,ab,by simpa only [rightSize,true_and] using fresh,ob⟩
    · have no : ¬a.reg 6 ≤ a.reg 1066 := by rw [one,flag,if_neg rightSize];decide
      have same : Between a a:=⟨fun _ _=>rfl,le_rfl,fun _ _=>rfl,sa.count,sa.available⟩
      exact ⟨a,_,.no no (.skip _),by have h:=Nat.one_le_pow 3 (d.n+1) (by omega);omega,same,
        (flag.trans (if_neg rightSize)).trans (if_neg (fun e=>rightSize e.1)).symm,rfl⟩
  obtain ⟨b,j,test_,jt,ab,both,bo⟩:=checked
  have zb:=compose za ab
  have unit:=(zb.control 6 (.inl rfl)).trans data.one
  obtain ⟨i,pre,ki⟩:=splitChain sizeList count
  rw [repCode]
  by_cases pass : c.length=level+1 ∧ rimOf d c=cut
  · have cutB:=input_kept cutA len test_ ab (by intro j lo hi;interval_cases j <;> decide)
    have rowB:=component_kept rowA test_ ab (by decide)
    obtain ⟨v,l,ex,lt,bv,vo⟩:=entries b cut seed zb valid cutB seedIn
      ((test_.preserves _ (by decide)).trans ((count.preserves _ (by decide)).trans idx)) head rowB pass.1 pass.2
    have enter : b.reg 6 ≤ b.reg 1066 := by rw [unit,both,if_pos pass]
    refine ⟨v,_,pre.continue _ (.seq test_ (.seq (.yes enter ex) (.skip _))),
      by ring_nf at kt jt ⊢ <;> omega,compose (compose sa ab) bv,?_⟩
    change v.output=s.output++visitTape Naming.name d level cut c
    simpa [visitTape,pass.1,pass.2,bo,out,c] using vo
  · have stop : ¬b.reg 6 ≤ b.reg 1066 := by rw [unit,both,if_neg pass];decide
    refine ⟨b,_,pre.continue _ (.seq test_ (.seq (.no stop (.skip _)) (.skip _))),
      by ring_nf at kt jt ⊢ <;> omega,compose sa ab,?_⟩
    change b.output=s.output++visitTape Naming.name d level cut c
    simpa [visitTape,pass] using bo.trans out
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

lemma from_entries (rep :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀level<x.n, let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      Scene.CutTraversal.Entries d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)))) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀level<x.n, let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      Scene.CutTraversal.Representatives d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ))) := by
  obtain ⟨c,D,b,per⟩:=rep
  refine ⟨2000*(c+1),D+3,b,?_⟩
  intro e ep e1 x s low high ready bounded r p rp pp bound key u prep v geo z menus level hl
  let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
  let w:=widthBound (e:ℝ)
  let E:=parameterEnvelope (e:ℝ)
  let V:=c*x.cap^D*x.n^(b*E)
  have each:=per e ep e1 x s low high ready bounded r p rp pp bound key u prep v geo z menus level hl
  have all_:=representative_program d w level V s.imem z (from_scene x s r _ w u v z prep geo menus)
    (edge_scene x s r _ w u v z prep geo menus) each
  change Representatives d w level s.imem z (2000*(c+1)*x.cap^(D+3)*x.n^(b*E))
  intro a cut seed ha valid input hs idx
  dsimp only
  intro head row
  obtain ⟨t,k,ex,kt,fr,ot⟩:=all_ a cut seed ha valid input hs idx head row
  refine ⟨t,k,ex,kt.trans ?_,fr,ot⟩
  have nc : x.n+1 ≤ x.cap := by dsimp [World.cap];omega
  have unit : 1 ≤ x.cap^D*x.n^(b*E) := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  have up : V+1 ≤ (c+1)*x.cap^D*x.n^(b*E) := by dsimp [V];rw [Nat.add_mul,Nat.add_mul,one_mul];omega
  change 2000*(V+1)*(x.n+1)^3 ≤ 2000*(c+1)*x.cap^(D+3)*x.n^(b*E)
  calc
    _ ≤ 2000*((c+1)*x.cap^D*x.n^(b*E))*x.cap^3 := Nat.mul_le_mul (Nat.mul_le_mul_left _ up) (Nat.pow_le_pow_left nc 3)
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
      Scene.CutTraversal.Representatives d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ))) := Scene.CutTraversal.from_entries Logical.Root.write_eligible_component_entries
