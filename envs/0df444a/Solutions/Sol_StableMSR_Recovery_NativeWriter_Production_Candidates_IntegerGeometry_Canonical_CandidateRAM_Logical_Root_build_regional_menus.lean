-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.build_regional_menus
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T05:33:50.355099+00:00
-- url     : https://prove2.me/submissions/3679c5ab-3fe5-4e66-a47f-87543c24e7f4

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_WindowSweep_complete_vertex_menu
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_menu_word_schedule_and_digits
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
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep
private def wordOps : List Program := [
  .op (.divide false 762 196 69),
  .op (.multiply 761 762 68),
  .op (.divide true 766 196 69),
  .op (.regular (.add 760 761 766)),
  .op (.regular (.copy 199 760)),
  .op (.save 76 196 199)
]
private def selectVertex : List Program := [
  .op (.regular (.copy 162 200)),
  .op (.regular (.copy 163 199)),
  .op (.regular (.copy 164 196))
]
private def vertexEnd : List Program := [
  .op (.regular (.copy 775 188))
]
private def vertexBody := chain (selectVertex++[src_data_for_vertex]++vertexEnd)
private def vertexLoop := forCount 200 774 64 vertexBody
private def wordBody := chain (wordOps++[vertexLoop])
private def wordLoop := forCount 196 759 70 wordBody
private lemma buildShape : Scene.buildMenus=chain [wordLoop] := by rfl

private inductive Field (n : ℕ) where
  | rep (p : Fin n) | first (p : Fin n) | touch (p : Fin n) | member (p q : Fin n) | feasible
  deriving DecidableEq

private inductive Site (n M : ℕ) where
  | word (i : Fin M)
  | slot (a : Fin n) (i : Fin M) (field : Field n)
  deriving DecidableEq

private def origin (n M j : ℕ) := cursorAt (offsets n M) j
private def Site.tag {n M : ℕ} : Site n M → ℕ
  | .word _ => 5
  | .slot _ _ (.rep _) => 6
  | .slot _ _ (.first _) => 7
  | .slot _ _ (.touch _) => 8
  | .slot _ _ (.member _ _) => 9
  | .slot _ _ .feasible => 10
private def Site.offset {n M : ℕ} : Site n M → ℕ
  | .word i => i.val
  | .slot a i (.rep p) | .slot a i (.first p) | .slot a i (.touch p) => (a.val*M+i.val)*n+p.val
  | .slot a i (.member p q) => ((a.val*M+i.val)*n+p.val)*n+q.val
  | .slot a i .feasible => a.val*M+i.val
private def Site.atHeap {n M : ℕ} (s : Site n M) := origin n M s.tag+s.offset
private def Site.wordId {n M : ℕ} : Site n M → ℕ
  | .word i | .slot _ i _ => i.val
private def Site.phase {n M : ℕ} : Site n M → ℕ
  | .word _ => 0
  | .slot a _ _ => a.val+1
private def Site.rank {n M : ℕ} (s : Site n M) := s.wordId*(n+1)+s.phase
private def wordAt (n h i : ℕ) := ((SingleCodes.words n h)[i]?).getD 0
private noncomputable def Site.expected {n M : ℕ} (m : ℤ → ℤ) (W : Cluster n) (h : ℕ) : Site n M → ℤ
  | .word i => (wordAt n h i.val:ℤ)
  | .slot a i f =>
    let U := Bits.win m W a
    let c := wordAt n h i.val
    let B := value U (rowBlock m U h c) (Bits.owner m (Bits.net m W)) a.val
    match f with
    | .rep p => B (.representative p)
    | .first p => B (.minimum p)
    | .touch p => B (.touch p)
    | .member p q => B (.member p q)
    | .feasible => if Bits.feasible U (Bits.blocks m U h c) then 1 else 0

private def slotLayout {n M : ℕ} (a : Fin n) (i : Fin M) (h cursor : ℕ) : Layout :=
  ⟨(a.val*M+i.val)*n,cursor+2*(h+1),origin n M 6,origin n M 7,origin n M 8,origin n M 9⟩

private lemma origin_mono (n M : ℕ) {i j : ℕ} (le : i ≤ j) : origin n M i ≤ origin n M j := by
  obtain ⟨tail,eq⟩ := List.take_prefix_take_left (l:=offsets n M) le
  simp [origin,cursorAt,← eq,List.map_append,List.sum_append]

private lemma flat_lt {n m i j : ℕ} (hi : i < n) (hj : j < m) : i*m+j < n*m := calc
  i*m+j < i*m+m := Nat.add_lt_add_left hj _
  _ = (i+1)*m := by ring
  _ ≤ n*m := Nat.mul_le_mul_right m hi
private lemma unflat {m i j k l : ℕ} (hj : j < m) (hl : l < m) (e : i*m+j=k*m+l) : i=k ∧ j=l := by
  rw [Nat.add_comm (i*m) j,Nat.add_comm (k*m) l] at e
  have hm := Nat.zero_lt_of_lt hj
  constructor
  · simpa only [Nat.add_mul_div_right _ _ hm,Nat.div_eq_of_lt hj,Nat.div_eq_of_lt hl,zero_add] using
      congrArg (fun x => x/m) e
  · simpa [Nat.add_mod,Nat.mod_eq_of_lt hj,Nat.mod_eq_of_lt hl] using congrArg (fun x => x%m) e

private lemma site_bounds {n M : ℕ} (s : Site n M) :
    5 ≤ s.tag ∧ s.tag ≤ 10 ∧ s.atHeap < origin n M (s.tag+1) := by
  cases s with
  | word i =>
    have := i.isLt
    simp [Site.atHeap,Site.tag,Site.offset,origin,cursorAt,offsets] <;> omega
  | slot a i f =>
    have aB := flat_lt a.isLt i.isLt
    have seedB (p : Fin n) := flat_lt aB p.isLt
    have memberB (p q : Fin n) := flat_lt (seedB p) q.isLt
    cases f with
    | rep p | first p | touch p =>
      have := seedB p
      simp [Site.tag,Site.atHeap,Site.offset,origin,cursorAt,offsets] <;> omega
    | member p q =>
      have := memberB p q
      simp [Site.tag,Site.atHeap,Site.offset,origin,cursorAt,offsets] <;> omega
    | feasible => simp [Site.tag,Site.atHeap,Site.offset,origin,cursorAt,offsets] <;> omega

private lemma site_arena {n M : ℕ} (s : Site n M) :
    origin n M 5 ≤ s.atHeap ∧ s.atHeap < origin n M 11 := by
  obtain ⟨lo,hi,inside⟩ := site_bounds s
  exact ⟨(origin_mono n M lo).trans (Nat.le_add_right _ _),inside.trans_le (origin_mono n M (by omega))⟩

private lemma loc_inj {n M : ℕ} : Function.Injective (Site.atHeap (n:=n) (M:=M)) := by
  intro s t e
  have notLt (a b : Site n M) (eq : a.atHeap=b.atHeap) (lt : a.tag < b.tag) : False := by
    have h1 := (site_bounds a).2.2
    have h2 : origin n M (a.tag+1) ≤ origin n M b.tag := origin_mono n M lt
    have h3 : origin n M b.tag ≤ b.atHeap := Nat.le_add_right _ _
    exact (h1.trans_le (h2.trans h3)).ne eq
  have tag : s.tag=t.tag := by
    rcases lt_trichotomy s.tag t.tag with lt|eq|gt
    · exact False.elim (notLt s t e lt)
    · exact eq
    · exact False.elim (notLt t s e.symm gt)
  have off : s.offset=t.offset := by simpa only [Site.atHeap,tag,Nat.add_right_inj] using e
  have oneSlot (a b : Fin n) (i j : Fin M) (h : a.val*M+i.val=b.val*M+j.val) : a=b ∧ i=j := by
    obtain ⟨x,y⟩ := unflat i.isLt j.isLt h
    exact ⟨Fin.ext x,Fin.ext y⟩
  have seedSlot (a b : Fin n) (i j : Fin M) (p q : Fin n)
      (h : (a.val*M+i.val)*n+p.val=(b.val*M+j.val)*n+q.val) : a=b ∧ i=j ∧ p=q := by
    obtain ⟨x,y⟩ := unflat p.isLt q.isLt h
    obtain ⟨v,w⟩ := oneSlot _ _ _ _ x
    exact ⟨v,w,Fin.ext y⟩
  cases s with
  | word i =>
    cases t with
    | word j => exact congrArg Site.word (Fin.ext off)
    | slot a j f => cases f <;> simp [Site.tag] at tag
  | slot a i f =>
    cases t with
    | word j => cases f <;> simp [Site.tag] at tag
    | slot b j g =>
      cases f <;> cases g <;> simp only [Site.tag] at tag <;> try contradiction
      all_goals simp only [Site.offset] at off
      case rep.rep p q | first.first p q | touch.touch p q =>
        obtain ⟨rfl,rfl,rfl⟩ := seedSlot _ _ _ _ p q off
        rfl
      case member.member p q u v =>
        obtain ⟨h,last⟩ := unflat q.isLt v.isLt off
        obtain ⟨rfl,rfl,rfl⟩ := seedSlot _ _ _ _ p u h
        cases Fin.ext last
        rfl
      case feasible.feasible =>
        obtain ⟨rfl,rfl⟩ := oneSlot _ _ _ _ off
        rfl

private lemma inputs_geometry {n M : ℕ} (a p : Fin n) :
    origin n M 3+a.val*n+p.val < origin n M 5 ∧ origin n M 1+p.val < origin n M 5 := by
  have h := flat_lt a.isLt p.isLt
  have lt := p.isLt
  simp [origin,cursorAt,offsets] <;> omega

private def place {n : ℕ} : Cell n → Field n
  | .mask p | .representative p => .rep p
  | .minimum p => .first p
  | .touch p => .touch p
  | .member p q => .member p q
private def permanent {n : ℕ} (z : Cell n) := ∀ p, z≠.mask p
private lemma embed_addr {n M h cursor : ℕ} (a : Fin n) (i : Fin M) (z : Cell n) (hp : permanent z) :
    (slotLayout a i h cursor).addr z=(Site.slot a i (place z)).atHeap := by
  cases z <;> simp_all [permanent,place,slotLayout,Layout.addr,Site.atHeap,Site.tag,Site.offset,Nat.add_assoc]
private lemma perm_or_mask {n : ℕ} (z : Cell n) : permanent z ∨ ∃p,z=.mask p := by
  classical
  by_cases h : ∃p,z=.mask p
  · exact .inr h
  · exact .inl (fun p eq => h ⟨p,eq⟩)
private lemma place_inj {n : ℕ} {z w : Cell n} (pz : permanent z) (pw : permanent w) (e : place z=place w) : z=w := by
  cases z <;> cases w <;> simp_all [permanent,place]
private lemma place_ne_menu {n : ℕ} (z : Cell n) : place z≠.feasible := by cases z <;> simp [place]
private lemma layout_below {n M h cursor : ℕ} (a : Fin n) (i : Fin M) (hc : origin n M 11 ≤ cursor)
    (z : Cell n) (p : permanent z) : (slotLayout a i h cursor).addr z < cursor := by
  rw [embed_addr a i z p]
  exact (site_arena _).2.trans_le hc
private lemma layout_floor {n M h cursor : ℕ} (a : Fin n) (i : Fin M) (hc : origin n M 11 ≤ cursor)
    (z : Cell n) : origin n M 5 ≤ (slotLayout a i h cursor).addr z := by
  rcases perm_or_mask z with yes|⟨p,rfl⟩
  · rw [embed_addr a i z yes];exact (site_arena _).1
  · have le := (origin_mono n M (show 5≤11 by decide)).trans hc
    simp [slotLayout,Layout.addr];omega
private lemma layout_separated {n M h cursor : ℕ} (a : Fin n) (i : Fin M) (hc : origin n M 11 ≤ cursor) :
    Separated n h cursor (origin n M 3+a.val*n) (origin n M 1) (slotLayout a i h cursor) := by
  constructor
  · intro z w eq
    rcases perm_or_mask z with p|⟨x,rfl⟩ <;> rcases perm_or_mask w with q|⟨y,rfl⟩
    · rw [embed_addr a i z p,embed_addr a i w q] at eq
      exact place_inj p q (Site.slot.inj (loc_inj eq)).2.2
    · have less := layout_below (h:=h) a i hc z p
      change (slotLayout a i h cursor).addr z=cursor+2*(h+1)+y.val at eq
      omega
    · have less := layout_below (h:=h) a i hc w q
      change cursor+2*(h+1)+x.val=(slotLayout a i h cursor).addr w at eq
      omega
    · simpa [Layout.addr,slotLayout,Fin.ext_iff] using eq
  · intro z j hj
    rcases perm_or_mask z with p|⟨p,rfl⟩
    · have lt := layout_below (h:=h) a i hc z p;omega
    · simp [Layout.addr,slotLayout];omega
  · intro z p
    exact ne_of_gt ((inputs_geometry (M:=M) a p).1.trans_le (layout_floor a i hc z))
  · intro z p
    exact ne_of_gt ((inputs_geometry (M:=M) a p).2.trans_le (layout_floor a i hc z))
private lemma apart {n M h cursor : ℕ} (a : Fin n) (i : Fin M) (hc : origin n M 11 ≤ cursor)
    (q : Site n M) (other : ∀ z : Cell n, q≠.slot a i (place z)) (z : Cell n) :
    (slotLayout a i h cursor).addr z≠q.atHeap := by
  rcases perm_or_mask z with p|⟨p,rfl⟩
  · rw [embed_addr a i z p];exact fun eq => other z (loc_inj eq).symm
  · have lt := (site_arena q).2.trans_le hc
    simp [Layout.addr,slotLayout];omega

private structure Progress {n M : ℕ} (m : ℤ → ℤ) (W : Cluster n) (h : ℕ) (v : State) (tick : ℕ) (t : State) : Prop where
  table : ∀ s : Site n M, t.heap s.atHeap=if s.rank < tick then s.expected m W h else 0
  geometry : ∀ z < origin n M 5,t.heap z=v.heap z
  cursor : (origin n M 11 : ℤ) ≤ t.reg 8
  output : t.output=v.output
  closed : t.closed=v.closed
private lemma Progress.assign {n M h tick : ℕ} {m : ℤ→ℤ} {W : Cluster n} {v t : State}
    (p : Progress (M:=M) m W h v tick t) {r : ℕ} (ne : 8≠r) (w : ℤ) :
    Progress (M:=M) m W h v tick (t.assign r w) :=
  ⟨p.table,p.geometry,by simpa [State.assign,ne] using p.cursor,p.output,p.closed⟩
private lemma rank_word {n M : ℕ} {i : Fin M} {s : Site n M} (eq : s.rank=i.val*(n+1)) : s=.word i := by
  cases s with
  | word j =>
    have e : j.val*(n+1)+0=i.val*(n+1)+0 := by simpa [Site.rank,Site.wordId,Site.phase] using eq
    exact congrArg Site.word (Fin.ext (unflat (by omega) (by omega) e).1)
  | slot a j f =>
    have e : j.val*(n+1)+(a.val+1)=i.val*(n+1)+0 := by simpa [Site.rank,Site.wordId,Site.phase] using eq
    have := (unflat (by have := a.isLt;omega) (by omega) e).2
    omega
private lemma rank_slot {n M : ℕ} {a : Fin n} {i : Fin M} {s : Site n M}
    (eq : s.rank=i.val*(n+1)+(a.val+1)) : ∃ f,s=.slot a i f := by
  cases s with
  | word j =>
    have e : j.val*(n+1)+0=i.val*(n+1)+(a.val+1) := by simpa [Site.rank,Site.phase,Site.wordId] using eq
    have := (unflat (by omega) (by have := a.isLt;omega) e).2;omega
  | slot b j f =>
    change j.val*(n+1)+(b.val+1)=i.val*(n+1)+(a.val+1) at eq
    obtain ⟨H,K⟩ := unflat (by have := b.isLt;omega) (by have := a.isLt;omega) eq
    exact ⟨f,by rw [show b=a from Fin.ext (by omega),show j=i from Fin.ext H]⟩

private def protectedReg (r : ℕ) := r=6 ∨ r=7 ∨ (64≤r ∧ r≤82)
private lemma safe_programs {r : ℕ} (inRange : protectedReg r) :
    writesReg r wordLoop=false ∧ writesReg r vertexLoop=false ∧ writesReg r (chain wordOps)=false ∧
      writesReg r (chain selectVertex)=false := by
  rcases inRange with rfl|rfl|⟨lo,hi⟩
  · decide
  · decide
  · interval_cases r <;> decide
private structure Regs (n h M : ℕ) (s : State) : Prop where
  one : s.reg 6=1
  zero : s.reg 7=0
  size : s.reg 64=(n:ℤ)
  height : s.reg 68=((h+1:ℕ):ℤ)
  rows : s.reg 69=(CartesianBallRows.rows n (h+1):ℤ)
  length : s.reg 70=(M:ℤ)
  ptr : ∀ j : Fin 11,s.reg (71+j.val)=(origin n M j.val:ℤ)
private lemma Regs.carry {n h M : ℕ} {s t : State} (rs : Regs n h M s)
    (fr : ∀r,protectedReg r → t.reg r=s.reg r) : Regs n h M t :=
  ⟨(fr 6 (.inl rfl)).trans rs.one,(fr 7 (.inr (.inl rfl))).trans rs.zero,(fr 64 (.inr (.inr (by decide)))).trans rs.size,
   (fr 68 (.inr (.inr (by decide)))).trans rs.height,(fr 69 (.inr (.inr (by decide)))).trans rs.rows,(fr 70 (.inr (.inr (by decide)))).trans rs.length,
   fun j => (fr (71+j.val) (.inr (.inr (by have := j.isLt;omega)))).trans (rs.ptr j)⟩

private structure Inputs {n : ℕ} (M : ℕ) (m : ℤ→ℤ) (W : Cluster n) (v : State) : Prop where
  window : ∀ a p : Fin n,v.heap (origin n M 3+a.val*n+p.val)=if p∈Bits.win m W a then 1 else 0
  owner : ∀ p : Fin n,v.heap (origin n M 1+p.val)=((Bits.owner m (Bits.net m W) p).val:ℤ)

private lemma after_word {n M h c : ℕ} {i : Fin M} {m : ℤ→ℤ} {W : Cluster n} {v z t : State}
    (pr : Progress (M:=M) m W h v (i.val*(n+1)) z) (code : wordAt n h i.val=c)
    (heap : t.heap=Function.update z.heap (Site.word (n:=n) i).atHeap (c:ℤ))
    (eight : t.reg 8=z.reg 8) (out : t.output=z.output) (cl : t.closed=z.closed) :
    Progress (M:=M) m W h v (i.val*(n+1)+1) t := by
  constructor
  · intro q
    by_cases eq : q=Site.word i
    · subst q;rw [heap,Function.update_self];simp [Site.rank,Site.phase,Site.wordId,Site.expected,code]
    · have addr : q.atHeap≠(Site.word (n:=n) i).atHeap := fun e => eq (loc_inj e)
      have different : q.rank≠i.val*(n+1) := fun e => eq (rank_word e)
      rw [heap,Function.update_of_ne addr,pr.table]
      by_cases lt : q.rank < i.val*(n+1)
      · rw [if_pos lt,if_pos (by omega)]
      · rw [if_neg lt,if_neg (by omega)]
  · intro j hj
    have floor := (site_arena (Site.word (n:=n) i)).1
    rw [heap,Function.update_of_ne (by omega)];exact pr.geometry _ hj
  · rw [eight];exact pr.cursor
  · exact out.trans pr.output
  · exact cl.trans pr.closed

private lemma after_slot {n M h g u cursor : ℕ} (a : Fin n) (i : Fin M)
    {m : ℤ→ℤ} {W : Cluster n} {v z t : State}
    (pr : Progress (M:=M) m W h v (i.val*(n+1)+(a.val+1)) z)
    (hc : origin n M 11 ≤ cursor) (code : wordAt n h i.val=SingleCodes.encode h g u)
    (done : VertexImage (slotLayout a i h cursor) (Bits.win m W a) m h (SingleCodes.encode h g u)
      (Bits.owner m (Bits.net m W)) a.val (Site.slot a i .feasible).atHeap cursor z t) :
    Progress (M:=M) m W h v (i.val*(n+1)+(a.val+1)+1) t := by
  constructor
  · intro q
    by_cases eq : ∃f,q=Site.slot a i f
    · obtain ⟨f,rfl⟩ := eq
      have lt : (Site.slot a i f).rank < i.val*(n+1)+(a.val+1)+1 := Nat.lt_succ_self _
      rw [if_pos lt]
      cases f with
      | rep p => simpa [Site.atHeap,Site.tag,Site.offset,Site.expected,slotLayout,Layout.addr,code] using done.cells (.representative p)
      | first p => simpa [Site.atHeap,Site.tag,Site.offset,Site.expected,slotLayout,Layout.addr,code] using done.cells (.minimum p)
      | touch p => simpa [Site.atHeap,Site.tag,Site.offset,Site.expected,slotLayout,Layout.addr,code] using done.cells (.touch p)
      | member p b => simpa [Site.atHeap,Site.tag,Site.offset,Site.expected,slotLayout,Layout.addr,code,Nat.add_assoc] using done.cells (.member p b)
      | feasible => simpa [Site.expected,code] using done.feasible
    · have ne : q.rank ≠ i.val*(n+1)+(a.val+1) := fun e => eq (rank_slot e)
      have addr : q.atHeap ≠ (Site.slot a i .feasible).atHeap := fun e => eq ⟨_,loc_inj e⟩
      rw [done.frame _ ((site_arena q).2.trans_le hc) addr (apart a i hc q (fun k e=>eq ⟨_,e⟩)),pr.table]
      by_cases lt : q.rank < i.val*(n+1)+(a.val+1)
      · rw [if_pos lt,if_pos (by omega)]
      · rw [if_neg lt,if_neg (by omega)]
  · intro j hj
    have low := (site_arena (Site.slot a i .feasible)).1
    have low' := (origin_mono n M (show 5≤11 by decide)).trans hc
    rw [done.frame _ (by omega) (by omega) (fun k => ne_of_gt (hj.trans_le (layout_floor a i hc k)))]
    exact pr.geometry _ hj
  · rw [done.nextCursor];exact_mod_cast (show origin n M 11 ≤ cursor+2*(h+1)+n by omega)
  · exact done.output.trans pr.output
  · exact done.closed.trans pr.closed

private def vertexCap (n h M : ℕ) := 41000*(n+1)^3*(h+1)*(M+1)
private def wordCap (n h M : ℕ) := 42000*(n+1)^4*(h+1)*(M+1)

private lemma pick_vertex (n : ℕ) (m : ℤ→ℤ) (s : State) :
    ∃ z, Executes n m (chain selectVertex) s z 7 ∧ z.reg 162=s.reg 200 ∧
      z.reg 163=s.reg 199 ∧ z.reg 164=s.reg 196 ∧ z.reg 8=s.reg 8 ∧ z.heap=s.heap ∧
      z.output=s.output ∧ z.closed=s.closed := by
  let t := ((s.assign 162 (s.reg 200)).assign 163 (s.reg 199)).assign 164 (s.reg 196)
  have run : Executes n m (chain selectVertex) s t 7 := evalLine_sound _ _ _ _ (by simp [selectVertex,chain,evalLine,Operation.next,regularNext,t,State.assign])
  exact ⟨t,run,by simp [t,State.assign],by simp [t,State.assign],by simp [t,State.assign],by simp [t,State.assign],rfl,rfl,rfl⟩

private lemma run_slot {n M h g u : ℕ} {m : ℤ→ℤ} {W : Cluster n} {v s : State}
    (a : Fin n) (i : Fin M) (hn : 0 < n) (hg : g < h+1) (hu : u < CartesianBallRows.rows n (h+1)) (um : u < M)
    (inputs : Inputs M m W v) (regs : Regs n h M s)
    (pr : Progress (M:=M) m W h v (i.val*(n+1)+(a.val+1)) s)
    (ai : s.reg 200=(a.val:ℤ)) (wi : s.reg 196=(i.val:ℤ)) (wc : s.reg 199=(SingleCodes.encode h g u:ℤ))
    (code : wordAt n h i.val=SingleCodes.encode h g u) :
    ∃ t k, Executes n m vertexBody s t k ∧ k≤vertexCap n h M ∧
      Progress (M:=M) m W h v (i.val*(n+1)+(a.val+1)+1) t := by
  classical
  obtain ⟨z,pick,va,wd,ix,reg8,heap,out,cl⟩ := pick_vertex n m s
  have zRegs := regs.carry (fun r hr => pick.preserves r (safe_programs hr).2.2.2)
  have atZ : Progress (M:=M) m W h v (i.val*(n+1)+(a.val+1)) z :=
    ⟨fun q => by rw [heap];exact pr.table q,fun q hq => by rw [heap];exact pr.geometry q hq,
      by rw [reg8];exact pr.cursor,out.trans pr.output,cl.trans pr.closed⟩
  let cursor := (z.reg 8).toNat
  have native : z.reg 8=(cursor:ℤ) := (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg _) atZ.cursor)).symm
  have hc : origin n M 11 ≤ cursor := by exact_mod_cast (atZ.cursor.trans_eq native)
  let L := slotLayout a i h cursor
  have floor := (origin_mono n M (show 5≤11 by decide)).trans hc
  obtain ⟨y,k,run,kt,info⟩ := complete_vertex_menu n h g u a.val M i.val cursor (origin n M 3) (origin n M 1)
    (origin n M 10) m z L (Bits.win m W a) (Bits.owner m (Bits.net m W)) hn hg hu rfl rfl
    zRegs.one zRegs.zero native zRegs.size zRegs.height zRegs.length
    (zRegs.ptr ⟨1,by decide⟩) (zRegs.ptr ⟨3,by decide⟩) (zRegs.ptr ⟨6,by decide⟩)
    (zRegs.ptr ⟨7,by decide⟩) (zRegs.ptr ⟨8,by decide⟩) (zRegs.ptr ⟨9,by decide⟩)
    (zRegs.ptr ⟨10,by decide⟩) (va.trans ai) (wd.trans wc) (ix.trans wi)
    (fun q => (atZ.geometry _ (inputs_geometry (M:=M) a q).1).trans (inputs.window a q))
    (fun q => (atZ.geometry _ (inputs_geometry (M:=M) a q).2).trans (inputs.owner q))
    (by intro b hb
        rw [show L.addr b=(Site.slot a i (place b)).atHeap from embed_addr a i b hb,atZ.table]
        exact if_neg (Nat.lt_irrefl _))
    (layout_below a i hc)
    (fun q => ⟨(inputs_geometry (M:=M) a q).1.trans_le floor,(inputs_geometry (M:=M) a q).2.trans_le floor⟩)
    (apart a i hc (.slot a i .feasible) (fun z e => place_ne_menu z (Site.slot.inj e).2.2.symm))
    (layout_separated a i hc)
  have atY := after_slot a i atZ hc code info
  let t := y.assign 775 (y.reg 188)
  have finish : Executes n m (chain vertexEnd) y t 3 := evalLine_sound _ _ _ _ rfl
  obtain ⟨p,start,ptime⟩ := splitChain selectVertex pick
  have bound : M+u+1≤2*(M+1) := by omega
  have mult := Nat.mul_le_mul_left (20000*(n+1)^3*(h+1)) bound
  refine ⟨t,_,start.continue _ (.seq run finish),?_,atY.assign (by decide) _⟩
  unfold vertexCap
  ring_nf at mult kt ⊢ <;> omega

private lemma run_word {n M h : ℕ} {m : ℤ→ℤ} {W : Cluster n} {v s : State}
    (i : Fin M) (hn : 0 < n) (count : M=sizes n h)
    (inputs : Inputs M m W v) (regs : Regs n h M s) (pr : Progress (M:=M) m W h v (i.val*(n+1)) s)
    (ix : s.reg 196=(i.val:ℤ)) :
    ∃ t k, Executes n m wordBody s t k ∧ k≤wordCap n h M ∧
      Progress (M:=M) m W h v ((i.val+1)*(n+1)) t := by
  let R := CartesianBallRows.rows n (h+1)
  let g := i.val/R
  let u := i.val%R
  have pos : 0 < R := pow_pos hn _
  have size : M=(h+1)*R := count
  have hg : g < h+1 := (Nat.div_lt_iff_lt_mul pos).mpr (size ▸ i.isLt)
  have hu : u < R := Nat.mod_lt _ pos
  have um : u < M := hu.trans_le (by rw [size];exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have coord : g*R+u=i.val := Nat.div_add_mod' _ _
  obtain ⟨word,t,d,dispatch,dt,codeReg,heap,out,cl⟩ := (Scene.menu_word_schedule_and_digits n h g u m hn hg hu).1
    (origin n M 5) s regs.one regs.height regs.rows (regs.ptr ⟨5,by decide⟩) (by simpa only [←coord] using ix)
  change Executes n m (chain wordOps) s t d at dispatch
  have code : wordAt n h i.val=SingleCodes.encode h g u := by
    change (SingleCodes.words n h)[g*R+u]?=some _ at word
    simp [wordAt,←coord,word]
  have table : t.heap=Function.update s.heap (Site.word (n:=n) i).atHeap (SingleCodes.encode h g u:ℤ) := by
    change t.heap=Function.update s.heap (origin n M 5+(g*R+u)) _ at heap
    rw [coord] at heap
    exact heap
  have initial := after_word pr code table (dispatch.preserves 8 (by decide)) out cl
  have rs := regs.carry (fun r hr => dispatch.preserves _ (safe_programs hr).2.2.1)
  let P := fun j z => Progress (M:=M) m W h v (i.val*(n+1)+(j+1)) z
  obtain ⟨z,k,loop,kt,done⟩ := GeometryTables.counted (n:=n) (m:=m) 200 774 64 n (vertexCap n h M) vertexBody t P
    (by decide) (by decide) (by decide) (by decide) rs.size initial (by
      intro j b r x e p;rcases e with rfl|rfl <;> exact p.assign (by decide) _) (by
      intro a ha w state fr ai
      obtain ⟨w',k,run,kt,next⟩ := run_slot (a:=⟨a,ha⟩) i hn hg hu um inputs
        (rs.carry (fun r hr => fr r (safe_programs hr).2.1)) state ai
        ((fr 196 (by decide)).trans ((dispatch.preserves _ (by decide)).trans ix))
        ((fr 199 (by decide)).trans codeReg) code
      exact ⟨w',k,run,kt,by simpa [P,Nat.add_assoc] using next⟩)
  obtain ⟨p,first,ptime⟩ := splitChain wordOps dispatch
  refine ⟨z,_,first.continue _ (.seq loop (.skip _)),?_,?_⟩
  · unfold wordCap
    unfold vertexCap at kt
    ring_nf at kt dt ⊢ <;> omega
  · change Progress m W h v (i.val*(n+1)+(n+1)) z at done
    simpa [Nat.succ_mul] using done

private lemma initial_tables {n h r w : ℕ} {m : ℤ→ℤ} {W : Cluster n} {s v : State}
    (init : Prepared n r h w s) (geo : Scene.GeometryImage m W h s v) :
    Inputs (sizes n h) m W v ∧ Regs n h (sizes n h) v ∧ Progress (M:=sizes n h) m W h v 0 v := by
  obtain ⟨one,zero,count,_,_,_,height,rows,length,_,cursor,ptr,clear,_,_⟩ := init
  have rs : Regs n h (sizes n h) s := ⟨one,zero,count,height,rows,length,ptr⟩
  have carried := rs.carry (t:=v) (by
    intro r h
    rcases h with h|h|h
    · exact geo.controls r (.inl h)
    · exact geo.controls r (.inr (.inl h))
    · exact geo.controls r (.inr (.inr (.inr h))))
  refine ⟨⟨fun a p => by simpa [origin,Nat.add_assoc] using geo.window a p,geo.owner⟩,carried,?_,?_,?_,rfl,rfl⟩
  · intro q;simp only [Nat.not_lt_zero,if_false];exact (geo.frame _ (site_arena q).1).trans (clear _ (site_arena q).2)
  · intro _ _;rfl
  · exact le_of_eq ((geo.controls 8 (.inr (.inr (.inl rfl)))).trans cursor).symm

private lemma full_table {n h : ℕ} {m : ℤ→ℤ} {W : Cluster n} {v t : State} {k : ℕ}
    (run : Executes n m wordLoop v t k)
    (ok : Progress (M:=sizes n h) m W h v (sizes n h*(n+1)) t) : Scene.RegionalMenus m W h v t := by
  classical
  let M := sizes n h
  have image (q : Site n M) : t.heap q.atHeap=q.expected m W h := by
    apply (ok.table q).trans (if_pos _)
    cases q with
    | word i => exact flat_lt i.isLt (show 0 < n+1 by omega)
    | slot a i f => exact flat_lt i.isLt (show a.val+1 < n+1 by have := a.isLt;omega)
  refine ⟨fun r hr => run.preserves _ (safe_programs hr).1,ok.cursor,ok.geometry,
    fun j hj => image (.word ⟨j,hj⟩),?_,ok.output,ok.closed⟩
  intro a j hj
  let i : Fin M := ⟨j,hj⟩
  let U := Bits.win m W a
  let C := rowBlock m U h (wordAt n h j)
  let R := representatives U C
  let own := Bits.owner m (Bits.net m W)
  have point (p : ℕ) (mem : p∈R) : ∃ b : Fin n,b.val=p ∧ b∈U := by
    obtain ⟨b,win,e⟩ := Finset.mem_image.mp (Finset.mem_filter.mp mem).1
    exact ⟨b,e,win⟩
  refine ⟨fun p => image (.slot a i (.rep p)),?_,?_,?_,image (.slot a i .feasible)⟩
  · intro b hb non
    obtain ⟨p,rfl,_⟩ := point b hb
    have res := image (.slot a i (.first p))
    change _=(if p.val∈R then (if ne : (C p.val).Nonempty then _ else _) else _) at res
    change p.val∈R at hb
    change (C p.val).Nonempty at non
    rw [if_pos hb,dif_pos non] at res
    exact res
  · intro b hb
    obtain ⟨p,rfl,_⟩ := point b hb
    have res := image (.slot a i (.touch p))
    change _=(if p.val∈R ∧ ∃ z∈C p.val,(own z).val=a.val then (1:ℤ) else 0) at res
    have eq : Bits.touchesB own a (C p.val)=true ↔ ∃z∈C p.val,(own z).val=a.val := by
      simp [Bits.touchesB,List.any_eq_true,Fin.ext_iff]
    change p.val∈R at hb
    change t.heap (Site.slot a i (.touch p)).atHeap=(if Bits.touchesB own a (C p.val) then (1:ℤ) else 0)
    by_cases yes : ∃z∈C p.val,(own z).val=a.val
    · exact (res.trans (if_pos ⟨hb,yes⟩)).trans (if_pos (eq.mpr yes)).symm
    · exact (res.trans (if_neg (fun e => yes e.2))).trans (if_neg (mt eq.mp yes)).symm
  · intro b hb q
    obtain ⟨p,rfl,win⟩ := point b hb
    have res := image (.slot a i (.member p q))
    change _=(if p∈U ∧ q∈C p.val then (1:ℤ) else 0) at res
    change t.heap (Site.slot a i (.member p q)).atHeap=(if q∈C p.val then (1:ℤ) else 0)
    by_cases yes : q∈C p.val
    · exact (res.trans (if_pos ⟨win,yes⟩)).trans (if_pos yes).symm
    · exact (res.trans (if_neg (fun e => yes e.2))).trans (if_neg yes).symm

private lemma run_menus {n h r w : ℕ} {m : ℤ→ℤ} {W : Cluster n} {s v : State}
    (hn : 0 < n) (init : Prepared n r h w s) (geo : Scene.GeometryImage m W h s v) :
    ∃t k, Executes n m Scene.buildMenus v t k ∧ k≤43000*(n+1)^4*(h+1)*(sizes n h+1)^2 ∧
      Scene.RegionalMenus m W h v t := by
  let M := sizes n h
  obtain ⟨inputs,regs,start⟩ := initial_tables init geo
  let P := fun j z => Progress (M:=M) m W h v (j*(n+1)) z
  obtain ⟨z,k,run,kt,done⟩ := GeometryTables.counted (n:=n) (m:=m) 196 759 70 M (wordCap n h M) wordBody v P
    (by decide) (by decide) (by decide) (by decide) regs.length (by simpa [P] using start)
    (by intro j b r x e pr;rcases e with rfl|rfl <;> exact pr.assign (by decide) _) (by
      intro j hj t good fr idx
      exact run_word ⟨j,hj⟩ hn rfl inputs (regs.carry (fun r hr => fr r (safe_programs hr).1)) good idx)
  rw [buildShape]
  refine ⟨z,_,.seq run (.skip _),?_,full_table run done⟩
  change 1+k+1 ≤ 43000*(n+1)^4*(h+1)*(M+1)^2
  unfold wordCap at kt
  ring_nf at kt ⊢ <;> omega

private lemma envelope_cost (x : World) (e : ℝ) (n2 : 2≤x.n) :
    43000*(x.n+1)^4*(budget e+1)*(sizes x.n (budget e)+1)^2 ≤
      172000*x.cap^4*x.n^(21*parameterEnvelope e) := by
  let H := budget e+1
  let E := parameterEnvelope e
  let n := x.n
  have Hlow : 1 ≤ H := Nat.succ_pos _
  have base : 2≤n := n2
  have hp : 0 < n := by omega
  have HE : H≤3*E := by
    have ol := Nat.le_mul_of_pos_right (ownerBound e) (Nat.succ_pos (widthBound e))
    change ownerBound e ≤ ownerBound e * (widthBound e+1) at ol
    dsimp [H,E,budget,parameterEnvelope]
    omega
  have hpH : H≤n^H := (Nat.le_of_lt (Nat.lt_two_pow_self (n:=H))).trans (Nat.pow_le_pow_left base H)
  have menuBound : sizes n (budget e)≤n^(3*H) := calc
    _ = H*n^(2*H) := rfl
    _ ≤ n^H*n^(2*H) := Nat.mul_le_mul_right _ hpH
    _ = n^(3*H) := by rw [←pow_add];congr 1 <;> omega
  have posPow : 0 < n^(3*H) := Nat.pow_pos hp
  have plus : sizes n (budget e)+1 ≤ 2*n^(3*H) := by omega
  have cap : n+1≤x.cap := by dsimp [n,World.cap];omega
  have prod := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 43000 (Nat.pow_le_pow_left cap 4)) hpH)
    (Nat.pow_le_pow_left plus 2)
  change 43000*(n+1)^4*H*(sizes n (budget e)+1)^2 ≤ 172000*x.cap^4*n^(21*E)
  apply prod.trans
  calc
    _ = 172000*x.cap^4*n^(7*H) := by
      rw [mul_pow,←pow_mul]
      have e7 : 7*H=H+(3*H)*2 := by omega
      rw [e7,pow_add]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp (by omega))

lemma run_region :
  ∃c D b:ℕ,∀e:ℚ,0 < e → e < 1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k < x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r < x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∃z k, Logical.Executes x.n s.imem Scene.buildMenus v z k ∧
      k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z := by
  refine ⟨172000,4,21,?_⟩
  intro e _ _ x s hk hn _ _ r p _ _ _ _ u init v geo
  obtain ⟨z,k,run,tim,res⟩ := run_menus (by omega) init geo
  exact ⟨z,k,run,tim.trans (envelope_cost x e (by omega)),res⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep

theorem solution
:
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∃z k, Logical.Executes x.n s.imem Scene.buildMenus v z k ∧
      k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.WindowSweep.run_region
