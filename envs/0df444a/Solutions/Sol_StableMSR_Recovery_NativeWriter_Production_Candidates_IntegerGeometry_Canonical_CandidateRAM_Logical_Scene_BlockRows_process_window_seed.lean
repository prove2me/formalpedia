-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.process_window_seed
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T05:07:17.044297+00:00
-- url     : https://prove2.me/submissions/b9d53983-53b4-48c0-a215-e2ddb61af621

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_fill_membership_row
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_first_distinct_row_scan
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_BlockRows_commit_representative_metadata
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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
private def sAddr : List Program := [
  .op (.regular (.add 459 165 173)),
  .op (.multiply 458 459 64),
  .op (.regular (.add 456 80 458)),
  .op (.regular (.copy 176 456))
]
private lemma address_for_seed (n b matrix p : ℕ) (m : ℤ → ℤ) (s : State)
    (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ)) (seed : s.reg 173=(p:ℤ)) (base : s.reg 165=(b:ℤ)) (mat : s.reg 80=(matrix:ℤ)) :
    ∃ t k,Executes n m (chain sAddr) s t k ∧ k ≤ 22+6*n ∧ t.reg 176=((matrix+(b+p)*n:ℕ):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃ t k,evalLine n m (chain sAddr) s=some (t,k) ∧ k ≤ 22+6*n ∧ t.reg 176=((matrix+(b+p)*n:ℕ):ℤ) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    simp [sAddr,chain,evalLine,Operation.next,regularNext,State.assign,one,sz,seed,base,mat,
      show 0 ≤ (b:ℤ)+p by omega] <;> omega
  obtain ⟨t,k,e,tm,w⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,w⟩

lemma process_seed
    (n h g u buf win b matrix mark rep minimum touch own vertex : ℕ)
    (m : ℤ → ℤ) (s : Logical.State) (W : Cluster n) (p : Fin n) (owner : Fin n → Fin n)
    (hp : p∈W) (hg : g<h+1)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (seed : s.reg 173=(p.val:ℤ))
    (digitsAt : s.reg 166=(buf:ℤ)) (balls : s.reg 169=(g:ℤ)) (window : s.reg 170=(win:ℤ))
    (baseAt : s.reg 165=(b:ℤ)) (matrixAt : s.reg 80=(matrix:ℤ)) (markAt : s.reg 171=(mark:ℤ))
    (repAt : s.reg 77=(rep:ℤ)) (minAt : s.reg 78=(minimum:ℤ)) (touchAt : s.reg 79=(touch:ℤ))
    (ownerAt : s.reg 72=(own:ℤ)) (vertexAt : s.reg 162=(vertex:ℤ))
    (digits : ∀ j < 2*(h+1), s.heap (buf+j)=(CartesianBallRows.digit n u j:ℤ))
    (inside : ∀ q : Fin n, 1 ≤ s.heap (win+q.val) ↔ q∈W)
    (owners : ∀ q : Fin n, s.heap (own+q.val)=((owner q).val:ℤ)) :
    let code := SingleCodes.encode h g u
    let C := rowBlock m W h code
    let R := representatives W C
    let key := b+p.val
    let dest := matrix+key*n
    (∀ q : Fin n, q∉W → s.heap (dest+q.val)=0) →
    (∀ i < p.val, 1 ≤ s.heap (mark+i) ↔ i∈R) →
    (∀ i < p.val, i∈R → ∀ q : Fin n, s.heap (matrix+(b+i)*n+q.val)=if q∈C i then 1 else 0) →
    (∀ i < n, ∀ j < 2*(h+1), dest+i ≠ buf+j) →
    (∀ i < n, ∀ j < n, dest+i ≠ win+j ∧ dest+i ≠ own+j ∧ dest+i ≠ mark+j) →
    (∀ a ∈ [mark+p.val,rep+key,minimum+key,touch+key], ∀ q : Fin n, a ≠ dest+q.val ∧ a ≠ own+q.val) →
    ∃ (t : Logical.State) (k : ℕ) (H : ℕ → ℤ), Logical.Executes n m seedWork s t k ∧
      k ≤ 6000*(n+1)^2*(h+1) ∧
      (∀ q : Fin n, H (dest+q.val)=if q∈C p.val then 1 else 0) ∧
      (∀ a, a<dest ∨ dest+n ≤ a → H a=s.heap a) ∧
      (let marked := Function.update (Function.update H (mark+p.val) 1) (rep+key) 1
       let withMin := if ne : (C p.val).Nonempty then Function.update marked (minimum+key) (((C p.val).min' ne).val:ℤ) else marked
       let committed := if ∃ q ∈ C p.val, (owner q).val=vertex then Function.update withMin (touch+key) 1 else withMin
       t.heap=if p.val∈R then committed else H) ∧
      t.reg 172=(if p.val∈R ∧ ¬(C p.val).Nonempty then 0 else s.reg 172) ∧
      t.output=s.output ∧ t.closed=s.closed
    := by
  classical
  dsimp only
  let code := SingleCodes.encode h g u
  let C := rowBlock m W h code
  let R := representatives W C
  let key := b+p.val
  let dest := matrix+key*n
  intro zero selected earlier digDisjoint arraysDisjoint fieldsDisjoint
  obtain ⟨a,i,addr,it,ptr,ah,ao,ac⟩ := address_for_seed n b matrix p.val m s one size seed baseAt matrixAt
  obtain ⟨v,j,fill,jt,bit,keep,vo,vc⟩ := fill_membership_row n h g u buf win dest m a W p hg
    ((addr.preserves 6 (by decide)).trans one) ((addr.preserves 64 (by decide)).trans size)
    ((addr.preserves 173 (by decide)).trans seed) ((addr.preserves 166 (by decide)).trans digitsAt)
    ((addr.preserves 169 (by decide)).trans balls) ((addr.preserves 170 (by decide)).trans window) ptr
    (by rw [ah];exact digits) (by rw [ah];exact inside) (by rw [ah];exact zero) digDisjoint
    (fun l hl z hz => (arraysDisjoint l hl z hz).1)
  have original (q : ℕ) (away : q<dest ∨ dest+n ≤ q) : v.heap q=s.heap q := (keep q away).trans (congrFun ah q)
  have outside (q : ℕ) (dis : ∀ l < n, dest+l ≠ q) : q < dest ∨ dest+n ≤ q := by
    by_contra no
    exact dis (q-dest) (by omega) (by omega)
  have cPoint : C p.val=Bits.block m W h code p := by simp [C,rowBlock,Bits.lookup,p.isLt]
  have newRow (q : Fin n) : v.heap (dest+q.val)=if q∈C p.val then 1 else 0 := by
    rw [cPoint]; exact bit q
  have fr (x : ℕ) (addrOff : writesReg x (chain sAddr)=false) (fillOff : writesReg x fillBlock=false) :
      v.reg x=s.reg x := (fill.preserves x fillOff).trans (addr.preserves x addrOff)
  have rowV := (fill.preserves 176 (by decide)).trans ptr
  obtain ⟨z,l,dup,lt,flag,zh,zo,zc⟩ := first_distinct_row_scan n b matrix mark m v W C p hp
    ((fr 6 (by decide) (by decide)).trans one) ((fr 64 (by decide) (by decide)).trans size)
    ((fr 165 (by decide) (by decide)).trans baseAt) ((fr 80 (by decide) (by decide)).trans matrixAt)
    ((fr 171 (by decide) (by decide)).trans markAt) ((fr 173 (by decide) (by decide)).trans seed) rowV
    (by intro x hx
        rw [original _ (outside _ (fun i hi => (arraysDisjoint i hi x (by omega)).2.2))]
        exact selected x hx)
    (by intro x hx q
        rcases hx with rfl|⟨hx,member⟩
        · exact newRow q
        · have before : matrix+(b+x)*n+q.val < dest := by
            have less : (b+x)*n+q.val < (b+p.val)*n := calc
              (b+x)*n+q.val < (b+x)*n+n := Nat.add_lt_add_left q.isLt _
              _ = (b+x+1)*n := by ring
              _ ≤ (b+p.val)*n := Nat.mul_le_mul_right n (by omega)
            dsimp [dest,key];omega
          rw [original _ (.inl before)]
          exact earlier x hx member q)
  let marked := Function.update (Function.update v.heap (mark+p.val) 1) (rep+key) 1
  let withMin := if ne : (C p.val).Nonempty then Function.update marked (minimum+key) (((C p.val).min' ne).val:ℤ) else marked
  let committed := if ∃ q∈C p.val,(owner q).val=vertex then Function.update withMin (touch+key) 1 else withMin
  have frZ (x : ℕ) (aOff : writesReg x (chain sAddr)=false) (fOff : writesReg x fillBlock=false)
      (dOff : writesReg x checkRepresentative=false) : z.reg x=s.reg x :=
    (dup.preserves x dOff).trans (fr x aOff fOff)
  have rowZ := (dup.preserves 176 (by decide)).trans rowV
  have oneZ := (frZ 6 (by decide) (by decide) (by decide)).trans one
  have finish : ∃ t k, Executes n m (instruction seedWork 8) z t k ∧ k ≤ 700*(n+1) ∧
      t.heap=(if p.val∈R then committed else v.heap) ∧
      t.reg 172=(if p.val∈R ∧ ¬(C p.val).Nonempty then 0 else s.reg 172) ∧
      t.output=z.output ∧ t.closed=z.closed := by
    change z.reg 177=(if p.val∈R then 1 else 0) at flag
    by_cases fresh : p.val∈R
    · obtain ⟨t,k,run,tm,tflag,theap,tout,tc⟩ := commit_representative_metadata n b mark rep minimum touch dest own p.val vertex m z
        (C p.val) owner (by simpa [fresh] using flag) oneZ ((frZ 64 (by decide) (by decide) (by decide)).trans size)
        ((frZ 173 (by decide) (by decide) (by decide)).trans seed)
        ((frZ 165 (by decide) (by decide) (by decide)).trans baseAt)
        ((frZ 171 (by decide) (by decide) (by decide)).trans markAt)
        ((frZ 77 (by decide) (by decide) (by decide)).trans repAt)
        ((frZ 78 (by decide) (by decide) (by decide)).trans minAt)
        ((frZ 79 (by decide) (by decide) (by decide)).trans touchAt) rowZ
        ((frZ 72 (by decide) (by decide) (by decide)).trans ownerAt)
        ((frZ 162 (by decide) (by decide) (by decide)).trans vertexAt)
        (by intro q; rw [zh,newRow q]; by_cases yes : q∈C p.val <;> simp [yes])
        (fun q => (congrFun zh _).trans ((original _ (outside _ (fun i hi => (arraysDisjoint i hi q.val q.isLt).2.1))).trans (owners q)))
        fieldsDisjoint
      refine ⟨t,k,run,tm,?_,?_,tout,tc⟩
      · simpa only [fresh,if_true,committed,withMin,marked,key,zh] using theap
      · by_cases ne : (C p.val).Nonempty <;> simp [tflag,fresh,ne,frZ 172 (by decide) (by decide) (by decide)]
    · have rz : z.reg 177=0 := by simpa [fresh] using flag
      have ex : Executes n m (instruction seedWork 8) z z 2 := .no (by rw [oneZ,rz];decide) (.skip z)
      exact ⟨z,2,ex,by omega,by simpa [fresh] using zh,by simpa [fresh] using frZ 172 (by decide) (by decide) (by decide),rfl,rfl⟩
  obtain ⟨t,k,last,kt,th,tflag,tout,tc⟩ := finish
  obtain ⟨i',ar,ia⟩ := splitChain sAddr addr
  obtain ⟨l',dr,ld⟩ := splitChain (((listOf seedWork).drop 5).take 3) dup
  have run := ar.continue _ (Executes.seq fill (dr.continue _ (.seq last (.skip _))))
  refine ⟨t,_,v.heap,run,?_,newRow,original,th,tflag,tout.trans (zo.trans (vo.trans ao)),tc.trans (zc.trans (vc.trans ac))⟩
  ring_nf at it jt lt kt ⊢ <;> omega

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
theorem solution
    (n h g u buf win b matrix mark rep minimum touch own vertex : ℕ)
    (m : ℤ → ℤ) (s : Logical.State) (W : Cluster n) (p : Fin n) (owner : Fin n → Fin n)
    (hp : p∈W) (hg : g<h+1)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (seed : s.reg 173=(p.val:ℤ))
    (digitsAt : s.reg 166=(buf:ℤ)) (balls : s.reg 169=(g:ℤ)) (window : s.reg 170=(win:ℤ))
    (baseAt : s.reg 165=(b:ℤ)) (matrixAt : s.reg 80=(matrix:ℤ)) (markAt : s.reg 171=(mark:ℤ))
    (repAt : s.reg 77=(rep:ℤ)) (minAt : s.reg 78=(minimum:ℤ)) (touchAt : s.reg 79=(touch:ℤ))
    (ownerAt : s.reg 72=(own:ℤ)) (vertexAt : s.reg 162=(vertex:ℤ))
    (digits : ∀ j < 2*(h+1), s.heap (buf+j)=(CartesianBallRows.digit n u j:ℤ))
    (inside : ∀ q : Fin n, 1 ≤ s.heap (win+q.val) ↔ q∈W)
    (owners : ∀ q : Fin n, s.heap (own+q.val)=((owner q).val:ℤ)) :
    let code := SingleCodes.encode h g u
    let C := rowBlock m W h code
    let R := representatives W C
    let key := b+p.val
    let dest := matrix+key*n
    (∀ q : Fin n, q∉W → s.heap (dest+q.val)=0) →
    (∀ i < p.val, 1 ≤ s.heap (mark+i) ↔ i∈R) →
    (∀ i < p.val, i∈R → ∀ q : Fin n, s.heap (matrix+(b+i)*n+q.val)=if q∈C i then 1 else 0) →
    (∀ i < n, ∀ j < 2*(h+1), dest+i ≠ buf+j) →
    (∀ i < n, ∀ j < n, dest+i ≠ win+j ∧ dest+i ≠ own+j ∧ dest+i ≠ mark+j) →
    (∀ a ∈ [mark+p.val,rep+key,minimum+key,touch+key], ∀ q : Fin n, a ≠ dest+q.val ∧ a ≠ own+q.val) →
    ∃ (t : Logical.State) (k : ℕ) (H : ℕ → ℤ), Logical.Executes n m seedWork s t k ∧
      k ≤ 6000*(n+1)^2*(h+1) ∧
      (∀ q : Fin n, H (dest+q.val)=if q∈C p.val then 1 else 0) ∧
      (∀ a, a<dest ∨ dest+n ≤ a → H a=s.heap a) ∧
      (let marked := Function.update (Function.update H (mark+p.val) 1) (rep+key) 1
       let withMin := if ne : (C p.val).Nonempty then Function.update marked (minimum+key) (((C p.val).min' ne).val:ℤ) else marked
       let committed := if ∃ q ∈ C p.val, (owner q).val=vertex then Function.update withMin (touch+key) 1 else withMin
       t.heap=if p.val∈R then committed else H) ∧
      t.reg 172=(if p.val∈R ∧ ¬(C p.val).Nonempty then 0 else s.reg 172) ∧
      t.output=s.output ∧ t.closed=s.closed
 := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.process_seed n h g u buf win b matrix mark rep minimum touch own vertex m s W p owner hp hg one size seed digitsAt balls window baseAt matrixAt markAt repAt minAt touchAt ownerAt vertexAt digits inside owners
