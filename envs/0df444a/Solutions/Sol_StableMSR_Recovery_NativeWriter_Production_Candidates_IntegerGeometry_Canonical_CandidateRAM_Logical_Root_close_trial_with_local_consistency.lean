-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.close_trial_with_local_consistency
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:59:39.192253+00:00
-- url     : https://prove2.me/submissions/2beb2afd-7637-4981-ad28-a5a9ecb201d5

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_regional_compatibility_from_tables
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_write_trial_close_record
import Definitions.Def_StableMSR_TrialLocalTest
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
      ∃t k,Executes N input body s t k ∧ k ≤ cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1)))
    (i rem:ℕ) (len:i+rem=n) (s:State) (start:P i s) (idx:s.reg ix=(i:ℤ)) (lim:s.reg last=(n:ℤ)-1) :
    ∃t k,Executes N input (.loop ix last (chain [body,.op (.regular (.inc ix))])) s t k ∧ k ≤ 1+rem*(cap+5) ∧ P n t :=by
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
      ∃t k,Executes N input body s t k ∧ k ≤ cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1))) :
    ∃t k,Executes N input (forCount ix last len body) s t k ∧ k ≤ 9+n*(cap+5) ∧ P n t :=by
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



open SingleCircuit TightLanguage Scene.SeparatorLevels
private structure Tables (d : Instance) (a : State) (M bits words : ℕ) : Prop where
  one : a.reg 6=1
  size : a.reg 64=(d.n:ℤ)
  base : a.reg 70=(M:ℤ)
  bitsAt : a.reg 81=(bits:ℤ)
  wordsAt : a.reg 76=(words:ℤ)
  positive : 0<M
  wordEnd : words+M ≤ (a.reg 8).toNat
  bitsEnd : bits+d.n*M ≤ (a.reg 8).toNat
  values : ∀ j<M, 0 ≤ a.heap (words+j) ∧ (a.heap (words+j)).toNat ≤ M
  menu : ∀ p<d.n, d.menu p = (List.range M).filterMap (fun j =>
    if 1 ≤ a.heap (bits+(p*M+j)) then some ((a.heap (words+j)).toNat) else none)

private lemma wordCount (n h : ℕ) : (SingleCodes.words n h).length = sizes n h := by
  have rect (H R : ℕ) (f : ℕ → ℕ → ℕ) :
      ((List.range H).flatMap fun i => (List.range R).map (f i)).length = H*R := by
    induction H with
    | zero => simp
    | succ H ih => simp [List.range_succ, List.flatMap_append, ih, Nat.succ_mul]
  exact rect (h+1) (n^(2*(h+1))) (SingleCodes.encode h)

private lemma listFromSlots (xs : List ℕ) :
    (List.range xs.length).map (fun i => xs[i]?.getD 0) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂; simp [List.getElem?_eq_getElem h₂]

private lemma representedTables (x : World) (s : Store) (r h w : ℕ) (u v z a : State)
    (hn : 0<x.n) (prep : Logical.Prepared x.n r h w u)
    (geometry : Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h u v)
    (menus : Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h v z)
    (preserved : Between z a) :
    let M := sizes x.n h
    let layout := offsets x.n M
    Tables (integerData x.n x.mem s.imem r h) a M (cursorAt layout 10) (cursorAt layout 5) := by
  let M := sizes x.n h
  let layout := offsets x.n M
  let W := WindowProfiles.piece x (r/x.n) (r%x.n)
  obtain ⟨u1,_,un,_,_,_,_,_,baseReg,_,_,ptrs,_,_,_⟩ := prep
  have ctrl (j : ℕ) (hj : j=6 ∨ (64 ≤ j ∧ j ≤ 81)) : a.reg j=u.reg j :=
    (preserved.control j (by rcases hj with h|h <;> omega)).trans
      ((menus.controls j (by rcases hj with h|h <;> omega)).trans (geometry.controls j (by rcases hj with h|h <;> omega)))
  have endWords : cursorAt layout 5+M ≤ cursorAt layout 11 := by simp [layout,cursorAt,offsets];omega
  have endBits : cursorAt layout 10+x.n*M ≤ cursorAt layout 11 := by simp [layout,cursorAt,offsets];omega
  have safe : cursorAt layout 11 ≤ (z.reg 8).toNat := by have := menus.cursor; dsimp [layout,M]; omega
  have cur := preserved.cursor
  refine ⟨(ctrl 6 (by decide)).trans u1,(ctrl 64 (by decide)).trans un,(ctrl 70 (by decide)).trans baseReg,
    (ctrl 81 (by decide)).trans (ptrs ⟨10,by decide⟩),(ctrl 76 (by decide)).trans (ptrs ⟨5,by decide⟩),
    by dsimp [M,sizes]; positivity,by change cursorAt layout 5+M ≤ _;omega,by change cursorAt layout 10+x.n*M ≤ _;omega,?_,?_⟩
  · intro j hj
    have wc := (preserved.tables (cursorAt layout 5+j) (by omega)).trans (menus.words j hj)
    change a.heap (cursorAt layout 5+j)=(((SingleCodes.words x.n h)[j]?.getD 0 : ℕ):ℤ) at wc
    rw [wc];simp only [Int.natCast_nonneg,Int.toNat_natCast,true_and]
    have hh : j<(SingleCodes.words x.n h).length := by rw [wordCount];exact hj
    rw [List.getElem?_eq_getElem hh,Option.getD_some]
    generalize heq : (SingleCodes.words x.n h)[j] = value
    have mem : value ∈ SingleCodes.words x.n h := heq ▸ List.getElem_mem hh
    change value ∈ (List.range (h+1)).flatMap (fun g=>(List.range (x.n^(2*(h+1)))).map (fun v=>SingleCodes.encode h g v)) at mem
    obtain ⟨g,hg,hits⟩ := List.mem_flatMap.mp mem
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hits
    have small := List.mem_range.mp hg
    have small' := List.mem_range.mp hv
    change v*(h+1)+g ≤ (h+1)*x.n^(2*(h+1))
    calc v*(h+1)+g ≤ (v+1)*(h+1) := by rw [Nat.succ_mul];omega
         _ ≤ _ := by rw [Nat.mul_comm (h+1)];exact Nat.mul_le_mul_right _ small'
  · intro p small
    change p<x.n at small
    let vertex : Fin x.n := ⟨p, small⟩
    let words := SingleCodes.words x.n h
    let valid := fun c => Bits.feasible (Bits.win s.imem W vertex)
      (Bits.blocks s.imem (Bits.win s.imem W vertex) h c)
    have len : words.length = M := wordCount _ _
    have menuEq : (integerData x.n x.mem s.imem r h).menu p = words.filter valid := by
      simp [integerData, arrange, Bits.normalized, Bits.lookup, small, Bits.menus, words, valid, vertex, W]
      rfl
    rw [menuEq]
    have listed : (List.range M).map (fun j => words[j]?.getD 0) = words := by
      rw [← len]; exact listFromSlots _
    calc
      words.filter valid = (List.range M).filterMap
          (fun j => if valid (words[j]?.getD 0) then some (words[j]?.getD 0) else none) := by
        conv_lhs => rw [← listed]
        rw [← List.filterMap_eq_filter, List.filterMap_map]
        rfl
      _ = _ := by
        apply List.filterMap_congr
        intro j hj
        have hj := List.mem_range.mp hj
        have slot : p*M+j < x.n*M := by
          calc p*M+j < p*M+M := Nat.add_lt_add_left hj _
               _ = (p+1)*M := (Nat.succ_mul _ _).symm
               _ ≤ _ := Nat.mul_le_mul_right _ small
        have endWords : cursorAt layout 5+M ≤ cursorAt layout 11 := by
          simp [layout,cursorAt,offsets]; omega
        have endBits : cursorAt layout 10+x.n*M ≤ cursorAt layout 11 := by
          simp [layout,cursorAt,offsets]; omega
        have safe : cursorAt layout 11 ≤ (z.reg 8).toNat := by have := menus.cursor; dsimp [layout,M]; omega
        have wc := (preserved.tables (cursorAt layout 5+j) (by omega)).trans (menus.words j hj)
        have fe := (preserved.tables (cursorAt layout 10+(p*M+j)) (by omega)).trans
          (menus.tables vertex j hj).2.2.2.2
        change a.heap (cursorAt layout 5+j) = ((words[j]?.getD 0 : ℕ):ℤ) at wc
        change a.heap (cursorAt layout 10+(p*M+j)) = (if valid (words[j]?.getD 0) then 1 else 0) at fe
        rw [wc, fe]
        cases valid (words[j]?.getD 0) <;> simp
private def enabled (d : Instance) (cut : List ℕ) (p : ℕ) := d.active p && !cut.contains p
private lemma allowed_eq (d : Instance) (cut : List ℕ) :
    allowed d cut=(List.range d.n).filter (enabled d cut) := by
  unfold allowed vertices
  rw [List.filter_filter]
  apply List.filter_congr;intro q _
  simp [enabled,Bool.and_comm]

private lemma form_piece (d : Instance) (cut : List ℕ) (seed : ℕ) (pos : 0 < d.n) :
    ∃f:ℕ→Bool, pieceAt d (allowed d cut) seed=(List.range d.n).filter f := by
  have hs : List.range d.n=List.range (d.n-1)++[d.n-1] := by rw [←List.range_succ];congr 1;omega
  unfold pieceAt
  rw [hs,List.foldl_append,List.foldl_cons,List.foldl_nil,allowed_eq,List.filter_filter,←hs]
  exact ⟨_,rfl⟩

private def decRow (M : ℕ) (val : ℕ→ℕ) (ok : ℕ→ℕ→Bool) (vs : List ℕ) :
    ℕ→Option Assignment := vs.foldr (fun v (k : ℕ→Option Assignment) q =>
      if ok v (q%M) then (k (q/M)).map (fun t=>t++[(v,val (q%M))]) else none) (fun _=>some [])

private lemma rowLabels (M : ℕ) (val lab : ℕ→ℕ) (ok : ℕ→ℕ→Bool) (vs : List ℕ) (q : ℕ) (a : Assignment)
    (accepted : decRow M val ok vs q=some a)
    (labels : ∀i (hi : i<vs.length),lab vs[i]=val ((q/M^i)%M)) :
    a=(vs.map (fun j=>(j,lab j))).reverse := by
  induction vs generalizing q a with
  | nil => simpa [decRow] using accepted.symm
  | cons v vs ih =>
    change (if ok v (q%M) then (decRow M val ok vs (q/M)).map (fun t=>t++[(v,val (q%M))]) else none)=_ at accepted
    split at accepted <;> try contradiction
    cases e : decRow M val ok vs (q/M) with
    | none => simp [e] at accepted
    | some tail =>
      have hd := labels 0 (by simp)
      have eq := ih (q/M) tail e (by
        intro i hi; have h := labels (i+1) (by simpa using hi)
        simpa [pow_succ,Nat.div_div_eq_div_mul,Nat.mul_comm M] using h)
      simpa [e,eq,List.reverse_cons,show lab v=val (q%M) by simpa using hd] using accepted.symm

private lemma canonicalFilter {xs : List ℕ} {n : ℕ} (ex : ∃p : ℕ→Bool,xs=(List.range n).filter p) :
    (List.range n).filter (fun j=>decide (j∈xs))=xs := by
  obtain ⟨p,rfl⟩:=ex
  apply List.filter_congr;intro j hj;cases h:p j <;> simp [List.mem_filter,h,hj]

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

private lemma mapValue (xs : List ℕ) (f : ℕ→ℕ) (p : ℕ) (hp:p∈xs) : value (xs.map (fun j=>(j,f j))) p=f p := by
  induction xs with
  | nil=>simp at hp
  | cons x xs ih=>
    by_cases eq:x=p
    · simp [value,eq]
    · have mem:p∈xs := (List.mem_cons.mp hp).resolve_left (Ne.symm eq)
      simpa [value,eq] using ih mem
private abbrev localReg : List ℕ := [6,64,70,75,77,79,80,224,225,226]
private abbrev keeps (u s : State) := ∀j∈localReg,u.reg j=s.reg j
private lemma unchanged {n m cmd s t k} (run: Executes n m cmd s t k) (safe:localReg.all (fun j=> !(writesReg j cmd))=true) : keeps t s := by
  intro j hj;apply run.preserves;simpa using List.all_eq_true.mp safe j hj
private abbrev bit (b:Bool) : ℤ := if b then 1 else 0
private structure PairData (n fee v rim graph table : ℕ) (m : ℤ→ℤ) (cut : ℕ→Bool) (idx : ℕ→ℕ)
    (edge fits : ℕ→ℕ→Bool) (s : State) : Prop where
  one : s.reg 6=1
  size : s.reg 64=(n:ℤ)
  vtx : s.reg 226=(v:ℤ)
  rimAt : s.reg 224=(rim:ℤ)
  graphAt : s.reg 75=(graph:ℤ)
  tabAt : s.reg 225=(table:ℤ)
  rimBits : ∀p<n,s.heap (rim+p)=bit (cut p)
  links : ∀i<n,∀p<n,s.heap (graph+(i*n+p))=bit (edge i p)
  cells : ∀p<n,p=v ∨ cut p=true → s.heap (table+p)=(idx p:ℤ)
  test : ∀i<n,∀j<n, i=v ∨ cut i=true → j=v ∨ cut j=true → ∀t:State,keeps t s → t.heap=s.heap →
    t.reg 203=(i:ℤ) → t.reg 204=(idx i:ℤ) → t.reg 205=(j:ℤ) → t.reg 206=(idx j:ℤ) →
    ∃u k,Executes n m src_fits t u k ∧ k ≤ fee ∧ u.reg 217=bit (fits i j) ∧ u.heap=t.heap ∧ u.closed=t.closed ∧ u.output=t.output
private lemma PairData.move {n fee v rim graph tab m cut idx edge fits s} (d : PairData n fee v rim graph tab m cut idx edge fits s)
    {u : State} (kept:keeps u s) (heap:u.heap=s.heap) : PairData n fee v rim graph tab m cut idx edge fits u := by
  refine ⟨(kept 6 (by decide)).trans d.one,(kept 64 (by decide)).trans d.size,(kept 226 (by decide)).trans d.vtx,
    (kept 224 (by decide)).trans d.rimAt,(kept 75 (by decide)).trans d.graphAt,(kept 225 (by decide)).trans d.tabAt,
    by simpa only [heap] using d.rimBits,by simpa only [heap] using d.links,by simpa only [heap] using d.cells,?_⟩
  intro i hi j hj ci cj t kt ht;exact d.test i hi j hj ci cj t (fun p hp=>(kt p hp).trans (kept p hp)) (ht.trans heap)
private def gate (ix a b tmp : ℕ) : List Program := [
  .cond ix 226 (.cond 226 ix (.op (.regular (.set a 1))) (.op (.regular (.set a 0)))) (.op (.regular (.set a 0))),
  .op (.regular (.copy b a)),.cond 6 b .skip (chain [.op (.fetch tmp 224 ix),.op (.regular (.copy b tmp))])]
private abbrev leftGate:=gate 231 988 987 991
private abbrev rightGate:=gate 236 997 996 1000
private def edgeRead : List Program := [.op (.multiply 1007 231 64),.op (.regular (.add 1006 1007 236)),.op (.fetch 1004 75 1006),.op (.regular (.copy 1003 1004))]
private def args : List Program := [.op (.fetch 1014 225 231),.op (.fetch 1018 225 236),.op (.regular (.copy 203 231)),.op (.regular (.copy 204 1014)),.op (.regular (.copy 205 236)),.op (.regular (.copy 206 1018))]
private def invert : List Program := [.op (.regular (.copy 1012 217)),.cond 6 1012 (.op (.regular (.set 1011 0))) (.op (.regular (.set 1011 1))),.op (.regular (.copy 1003 1011))]
private def fitBranch :=chain (args++[src_fits]++invert)
private def clearFlag :=chain [.op (.regular (.set 1021 0)),.op (.regular (.copy 233 1021))]
private def pairCmd :=chain (edgeRead++[.cond 6 1003 fitBranch .skip,.cond 6 1003 clearFlag .skip])
private def innerCmd :=chain (rightGate++[.cond 6 996 pairCmd .skip])
private def innerLoop:=forCount 236 995 64 innerCmd
private def outerCmd:=chain (leftGate++[.cond 6 987 innerLoop .skip])
private def outerLoop:=forCount 231 986 64 outerCmd
private lemma outerGuard {n fee v rim graph tab m cut idx edge fits s} (d : PairData n fee v rim graph tab m cut idx edge fits s)
    (i : ℕ) (small:i<n) (ix:s.reg 231=(i:ℤ)) :
    ∃t k,Executes n m (chain leftGate) s t k ∧ k ≤ 100 ∧ (1 ≤ t.reg 987 ↔ i=v ∨ cut i=true) ∧ t.heap=s.heap ∧ t.closed=s.closed ∧ t.output=s.output := by
  let res:=(evalLine n m (chain leftGate) s).getD (s,0)
  have nz : 0 ≤ (rim:ℤ)+i := by omega
  have ad : ((rim:ℤ)+i).toNat=rim+i := by omega
  have bits:=d.rimBits i small
  refine ⟨res.1,res.2,evalLine_sound _ _ _ _ ?_,?_,?_,?_,?_,?_⟩ <;>
    by_cases le:i ≤ v <;> by_cases ge:v ≤ i <;> cases c:cut i <;>
    simp [res,leftGate,gate,chain,evalLine,Operation.next,regularNext,State.assign,ix,d.vtx,d.rimAt,d.one,ad,nz,le,ge,bits,c,bit] <;> omega
private lemma innerGuard {n fee v rim graph tab m cut idx edge fits s} (d : PairData n fee v rim graph tab m cut idx edge fits s)
    (i : ℕ) (small:i<n) (ix:s.reg 236=(i:ℤ)) :
    ∃t k,Executes n m (chain rightGate) s t k ∧ k ≤ 100 ∧ (1 ≤ t.reg 996 ↔ i=v ∨ cut i=true) ∧ t.heap=s.heap ∧ t.closed=s.closed ∧ t.output=s.output := by
  let res:=(evalLine n m (chain rightGate) s).getD (s,0)
  have nz : 0 ≤ (rim:ℤ)+i := by omega
  have ad : ((rim:ℤ)+i).toNat=rim+i := by omega
  have bits:=d.rimBits i small
  refine ⟨res.1,res.2,evalLine_sound _ _ _ _ ?_,?_,?_,?_,?_,?_⟩ <;>
    by_cases le:i ≤ v <;> by_cases ge:v ≤ i <;> cases c:cut i <;>
    simp [res,rightGate,gate,chain,evalLine,Operation.next,regularNext,State.assign,ix,d.vtx,d.rimAt,d.one,ad,nz,le,ge,bits,c,bit] <;> omega
private lemma doFits {n fee v rim graph tab m cut idx edge fits s} (d : PairData n fee v rim graph tab m cut idx edge fits s)
    (i j : ℕ) (hi:i<n) (hj:j<n) (ci:i=v ∨ cut i=true) (cj:j=v ∨ cut j=true)
    (li:s.reg 231=(i:ℤ)) (ri:s.reg 236=(j:ℤ)) :
    ∃t k,Executes n m fitBranch s t k ∧ k ≤ fee+170 ∧ t.reg 1003=bit (!(fits i j)) ∧ t.heap=s.heap ∧ t.closed=s.closed ∧ t.output=s.output := by
  let a:=(((((s.assign 1014 (idx i:ℤ)).assign 1018 (idx j:ℤ)).assign 203 (i:ℤ)).assign 204 (idx i:ℤ)).assign 205 (j:ℤ)).assign 206 (idx j:ℤ)
  have aa : 0 ≤ (tab:ℤ)+i := by omega
  have ab : 0 ≤ (tab:ℤ)+j := by omega
  have ai : ((tab:ℤ)+i).toNat=tab+i := by omega
  have aj : ((tab:ℤ)+j).toNat=tab+j := by omega
  have first : Executes n m (chain args) s a 139 := by
    apply evalLine_sound;simp [args,chain,evalLine,Operation.next,regularNext,a,State.assign,d.tabAt,li,ri,aa,ab,ai,aj,d.cells _ hi ci,d.cells _ hj cj]
  obtain ⟨u,k,run,bt,flag,heap,cl,out⟩:=d.test i hi j hj ci cj a (unchanged first (by decide)) rfl
      (by simp [a,State.assign]) (by simp [a,State.assign]) (by simp [a,State.assign]) (by simp [a,State.assign])
  have u1: u.reg 6=1 := (run.preserves 6 (by decide)).trans ((first.preserves 6 (by decide)).trans d.one)
  let t:=((u.assign 1012 (u.reg 217)).assign 1011 (bit (!(fits i j)))).assign 1003 (bit (!(fits i j)))
  have inv : ∃z,Executes n m (chain invert) u t z ∧ z ≤ 12 := by
    cases yes:fits i j <;> refine ⟨8,evalLine_sound _ _ _ _ ?_,by decide⟩ <;>
      simp [invert,chain,evalLine,Operation.next,regularNext,t,State.assign,flag,u1,yes,bit]
  obtain ⟨z,inv,tm⟩:=inv
  obtain ⟨c,pre,eq⟩:=splitChain args first
  exact ⟨t,_,pre.continue _ (.seq run inv),by omega,by simp [t,State.assign],heap,cl,out⟩
private lemma checkPair {n fee v rim graph tab m cut idx edge fits s} (d : PairData n fee v rim graph tab m cut idx edge fits s)
    (i j : ℕ) (hi:i<n) (hj:j<n) (ci:i=v ∨ cut i=true) (cj:j=v ∨ cut j=true)
    (li:s.reg 231=(i:ℤ)) (ri:s.reg 236=(j:ℤ)) (start:Bool) (flag:s.reg 233=bit start) :
    ∃t k,Executes n m pairCmd s t k ∧ k ≤ fee+300+6*n ∧ t.reg 233=bit (start && (!(edge i j) || fits i j)) ∧
      t.heap=s.heap ∧ t.closed=s.closed ∧ t.output=s.output := by
  let off:=i*n+j
  let a:=(((s.assign 1007 ((i*n:ℕ):ℤ)).assign 1006 (off:ℤ)).assign 1004 (bit (edge i j))).assign 1003 (bit (edge i j))
  have aa : 0 ≤ (graph:ℤ)+((i:ℤ)*n+j) := by positivity
  have ad : ((graph:ℤ)+((i:ℤ)*n+j)).toNat=graph+(i*n+j) := by exact_mod_cast (Int.toNat_natCast (graph+(i*n+j)))
  have read : Executes n m (chain edgeRead) s a (79+6*n) := by
    apply evalLine_sound;simp [edgeRead,chain,evalLine,Operation.next,regularNext,State.assign,a,off,d.graphAt,li,ri,d.one,d.size,aa,ad,d.links _ hi _ hj]
    <;> omega
  have a1:=(read.preserves 6 (by decide)).trans d.one
  have af : a.reg 1003=bit (edge i j) := by simp [a,State.assign]
  have R : ∃u k,Executes n m (.cond 6 1003 fitBranch .skip) a u k ∧ k ≤ fee+171 ∧ u.reg 1003=bit (edge i j && !(fits i j)) ∧
      u.heap=s.heap ∧ u.closed=s.closed ∧ u.output=s.output := by
    cases e:edge i j with
    | false=>exact ⟨a,_,.no (by rw [af,a1,e];decide) (.skip _),by omega,by simp [af,e],rfl,rfl,rfl⟩
    | true=>
      obtain ⟨u,k,ex,bt,f,heap,cl,out⟩:=doFits (d.move (unchanged read (by decide)) rfl) i j hi hj ci cj
        ((read.preserves 231 (by decide)).trans li) ((read.preserves 236 (by decide)).trans ri)
      exact ⟨u,_,.yes (by rw [af,a1,e];decide) ex,by omega,by simpa [e] using f,heap,cl,out⟩
  obtain ⟨u,k,ch,bt,bad,heap,cl,out⟩:=R
  have u1:=(ch.preserves 6 (by decide)).trans a1
  have uf:=(ch.preserves 233 (by decide)).trans ((read.preserves 233 (by decide)).trans flag)
  obtain ⟨c,pr,eq⟩:=splitChain edgeRead read
  cases e:edge i j <;> cases f:fits i j
  all_goals first
    | exact ⟨_,_,pr.continue _ (.seq ch (.seq (.no (by rw [u1,bad,e,f];decide) (.skip _)) (.skip _))),by omega,by simpa [e,f] using uf,heap,cl,out⟩
    | have clear : Executes n m clearFlag u ((u.assign 1021 0).assign 233 0) 5 := by apply evalLine_sound;rfl
      exact ⟨_,_,pr.continue _ (.seq ch (.seq (.yes (by rw [u1,bad,e,f];decide) clear) (.skip _))),by omega,by simp [e,f,State.assign,bit],heap,cl,out⟩
private def activeOn (v : ℕ) (cut : ℕ→Bool) (p : ℕ) := decide (p=v) || cut p
private def pairOK (v : ℕ) (cut : ℕ→Bool) (edge fits : ℕ→ℕ→Bool) (i j : ℕ) := !(activeOn v cut j) || !edge i j || fits i j
private def rowOK (n v : ℕ) (cut : ℕ→Bool) (edge fits : ℕ→ℕ→Bool) (i : ℕ) := !(activeOn v cut i) || (List.range n).all (pairOK v cut edge fits i)
private lemma innerAll {n fee v rim graph tab m cut idx edge fits s} (d : PairData n fee v rim graph tab m cut idx edge fits s)
    (i : ℕ) (hi:i<n) (ci:i=v ∨ cut i=true) (li:s.reg 231=(i:ℤ)) (start:Bool) (flag:s.reg 233=bit start) :
    ∃t k,Executes n m innerLoop s t k ∧ k ≤ 9+n*(fee+415+6*n) ∧
    t.reg 233=bit (start && (List.range n).all (pairOK v cut edge fits i)) ∧ t.heap=s.heap ∧ t.closed=s.closed ∧ t.output=s.output := by
  let P:=fun j (u:State)=>u.reg 233=bit (start && (List.range j).all (pairOK v cut edge fits i)) ∧ u.heap=s.heap ∧ u.closed=s.closed ∧ u.output=s.output
  have stable (j : ℕ) (hj:j∈localReg) : writesReg j innerLoop=false := by
    have h : localReg.all (fun j=> !(writesReg j innerLoop))=true := by decide
    simpa using List.all_eq_true.mp h j hj
  obtain ⟨t,k,ex,tm,next⟩:=Scene.GeometryTables.counted 236 995 64 n (fee+410+6*n) innerCmd s P (by decide) (by decide) (by decide) (by decide) d.size (by simpa [P] using flag) (by
    intro j u a x h ok;rcases h with rfl|rfl <;> simpa [P,State.assign] using ok) (by
    intro j hj u good fr ix
    obtain ⟨flag,heap,cl,out⟩:=good
    have du:=d.move (fun r hr=>fr _ (stable r hr)) heap
    obtain ⟨a,k,guard,bt,hit,ah,ac,ao⟩:=innerGuard du j hj ix
    obtain ⟨c,pr,eq⟩:=splitChain rightGate guard
    have a1:=(guard.preserves 6 (by decide)).trans du.one
    have af:=(guard.preserves 233 (by decide)).trans flag
    by_cases cj:j=v ∨ cut j=true
    all_goals first
      | have act:activeOn v cut j=true := by simpa [activeOn] using cj
        obtain ⟨t,l,run,tm,res,hh,cc,oo⟩:=checkPair (du.move (unchanged guard (by decide)) ah) i j hi hj ci cj
          ((guard.preserves 231 (by decide)).trans ((fr 231 (by decide)).trans li)) ((guard.preserves 236 (by decide)).trans ix) _ af
        refine ⟨t,_,pr.continue _ (.seq (.yes (a1 ▸ hit.mpr cj) run) (.skip _)),by omega,?_,hh.trans (ah.trans heap),cc.trans (ac.trans cl),oo.trans (ao.trans out)⟩
        simpa [pairOK,act,List.range_succ,List.all_append,Bool.and_assoc] using res
      | have act:activeOn v cut j=false := by simpa [activeOn,not_or] using cj
        refine ⟨a,_,pr.continue _ (.seq (.no (by rw [a1];exact fun h=>cj (hit.mp h)) (.skip _)) (.skip _)),by omega,?_,ah.trans heap,ac.trans cl,ao.trans out⟩
        simpa [pairOK,act,List.range_succ,List.all_append] using af)
  exact ⟨t,k,ex,by ring_nf at tm ⊢;omega,next⟩
private lemma outerAll {n fee v rim graph tab m cut idx edge fits s} (d : PairData n fee v rim graph tab m cut idx edge fits s)
    (flag:s.reg 233=1) :
    ∃t k,Executes n m outerLoop s t k ∧ k ≤ 9+n*(130+n*(fee+415+6*n)) ∧
    t.reg 233=bit ((List.range n).all (rowOK n v cut edge fits)) ∧ t.heap=s.heap ∧ t.closed=s.closed ∧ t.output=s.output := by
  let P:=fun j (u:State)=>u.reg 233=bit ((List.range j).all (rowOK n v cut edge fits)) ∧ u.heap=s.heap ∧ u.closed=s.closed ∧ u.output=s.output
  have stable (j : ℕ) (hj:j∈localReg) : writesReg j outerLoop=false := by
    have h : localReg.all (fun j=> !(writesReg j outerLoop))=true := by decide
    simpa using List.all_eq_true.mp h j hj
  obtain ⟨t,k,ex,tm,next⟩:=Scene.GeometryTables.counted 231 986 64 n (125+n*(fee+415+6*n)) outerCmd s P (by decide) (by decide) (by decide) (by decide) d.size
    (by simpa [P,bit] using flag) (by intro j u a x h ok;rcases h with rfl|rfl <;> simpa [P,State.assign] using ok) (by
    intro i hi u good fr ix
    obtain ⟨flag,heap,cl,out⟩:=good
    have du:=d.move (fun r hr=>fr _ (stable r hr)) heap
    obtain ⟨a,k,guard,bt,hit,ah,ac,ao⟩:=outerGuard du i hi ix
    obtain ⟨c,pr,eq⟩:=splitChain leftGate guard
    have a1:=(guard.preserves 6 (by decide)).trans du.one
    have af:=(guard.preserves 233 (by decide)).trans flag
    by_cases ci:i=v ∨ cut i=true
    · have act:activeOn v cut i=true := by simpa [activeOn] using ci
      obtain ⟨t,l,run,tm,res,hh,cc,oo⟩:=innerAll (du.move (unchanged guard (by decide)) ah) i hi ci ((guard.preserves 231 (by decide)).trans ix) _ af
      refine ⟨t,_,pr.continue _ (.seq (.yes (a1 ▸ hit.mpr ci) run) (.skip _)),by omega,?_,hh.trans (ah.trans heap),cc.trans (ac.trans cl),oo.trans (ao.trans out)⟩
      simpa [rowOK,act,List.range_succ,List.all_append] using res
    · have act:activeOn v cut i=false := by simpa [activeOn,not_or] using ci
      refine ⟨a,_,pr.continue _ (.seq (.no (by rw [a1];exact fun h=>ci (hit.mp h)) (.skip _)) (.skip _)),by omega,?_,ah.trans heap,ac.trans cl,ao.trans out⟩
      simpa [rowOK,act,List.range_succ,List.all_append] using af)
  exact ⟨t,k,ex,by ring_nf at tm ⊢;omega,next⟩
private lemma allLabels (d : Instance) (v : ℕ) (cut : ℕ→Bool) (keys : List ℕ) (word : ℕ→ℕ)
    (mem : ∀p,p∈keys ↔ p<d.n ∧ activeOn v cut p=true) :
    (List.range d.n).all (rowOK d.n v cut d.edge (fun i j=>d.test i j (word i) (word j))) =
    localOK d (keys.map (fun p=>(p,word p))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [localOK,List.all_map,List.all_eq_true,List.mem_range,Function.comp_apply]
  constructor
  · intro h i hi j hj
    obtain ⟨bi,ai⟩:=(mem i).mp hi
    obtain ⟨bj,aj⟩:=(mem j).mp hj
    have r:=h i bi
    simp only [rowOK,ai,Bool.not_true,Bool.false_or,List.all_eq_true,List.mem_range] at r
    simpa [pairOK,aj] using r j bj
  · intro h i bi
    by_cases ai:activeOn v cut i=true
    · simp only [rowOK,ai,Bool.not_true,Bool.false_or,List.all_eq_true,List.mem_range]
      intro j bj;by_cases aj:activeOn v cut j=true
      · simpa [pairOK,aj] using h i ((mem i).mpr ⟨bi,ai⟩) j ((mem j).mpr ⟨bj,aj⟩)
      · simp [pairOK,Bool.eq_false_iff.mpr aj]
    · simp [rowOK,Bool.eq_false_iff.mpr ai]
private lemma localCost (n cap : ℕ) (e : ℚ) (hn:2 ≤ n) (hc:n+1 ≤ cap) (ep:0<e) (el:e<1) :
    let M:=sizes n (budget (e:ℝ))
    5+(9+n*(130+n*(1000*(M+1)+1000*(n+1)^3+415+6*n)))+(300+n*(165+6*n)) ≤ 10000*cap^5*n^(15*parameterEnvelope (e:ℝ)) := by
  let O := ownerBound (e:ℝ)
  let E := parameterEnvelope (e:ℝ)
  let W := widthBound (e:ℝ)
  let H := budget (e:ℝ)+1
  let M := sizes n (budget (e:ℝ))
  let F := n^(15*E)
  have er : (0:ℝ)<e := by exact_mod_cast ep
  have er' : (e:ℝ)<1 := by exact_mod_cast el
  have op : 1 ≤ O := by
    unfold O ownerBound; apply Nat.le_floor; rw [le_div_iff₀ er]; norm_num; linarith
  have hH : H ≤ 5*O := by dsimp [H,budget,O] at *; omega
  have OW : O*(W+1) ≤ E := by dsimp [O,W,E,parameterEnvelope]; omega
  have O1 : O ≤ E := (by simpa using Nat.mul_le_mul_left O (show 1 ≤ W+1 by omega) : O ≤ O*(W+1)).trans OW
  have Hn : H ≤ n^H := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left hn _)
  have M0 : M ≤ n^(3*H) := by
    change H*n^(2*H) ≤ _
    calc H*n^(2*H) ≤ n^H*n^(2*H) := Nat.mul_le_mul_right _ Hn
         _ = _ := by rw [← pow_add]; congr 1; omega
  have MF : M ≤ F := M0.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have fp : 1 ≤ F := Nat.pow_pos (by omega)
  have z := Nat.mul_le_mul (Nat.pow_le_pow_left hc 5) (show M+1 ≤ F*2 by omega)
  calc _ ≤ 5000*((n+1)^5*(M+1)) := by change 5+(9+n*(130+n*(1000*(M+1)+1000*(n+1)^3+415+6*n)))+(300+n*(165+6*n)) ≤ _;ring_nf;omega
       _ ≤ 5000*(cap^5*(F*2)) := Nat.mul_le_mul_left _ z
       _ = _ := by change _=10000*cap^5*F;ring
private def initLocal : List Program := [.op (.regular (.set 984 1)),.op (.regular (.copy 233 984))]
private lemma closeFrameReg (r : ℕ) (hr : r=6 ∨ r=7 ∨ r=8 ∨ (64 ≤ r ∧ r ≤ 81) ∨ r∈[241,242,243,247,250]) :
    writesReg r (chain ((listOf src_trial).drop 10))=false := by
  rcases hr with rfl|rfl|rfl|small|hs
  · decide
  · decide
  · decide
  · have all : ∀i:Fin 82,64 ≤ i.val → writesReg i.val (chain ((listOf src_trial).drop 10))=false := by decide
    exact all ⟨r,by omega⟩ small.1
  · simp at hs;rcases hs with h|h|h|h|h <;> subst r <;> decide

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open Scene.CutTraversal Scene.SeparatorLevels TightLanguage SingleCircuit
theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀level<x.n, let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      Scene.CutTraversal.LocalTrials d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ))) := by
  refine ⟨10000,5,15,?_⟩
  intro e ep el x s hk hkn ready bounded r p pr pp rr key u prep g geo z menus level hl
  let h:=budget (e:ℝ)
  let M:=sizes x.n h
  let layout:=offsets x.n M
  let bits:=cursorAt layout 10
  let words:=cursorAt layout 5
  let d:=integerData x.n x.mem s.imem r h
  let E:=parameterEnvelope (e:ℝ)
  change LocalTrials d _ level s.imem z _
  intro a cut seed az hc inp hs rs
  dsimp only
  intro hd carg len rim q hq row ok v hv j hj permitted t F cp bp sp vert slot wrote
  let C:=pieceAt d (allowed d cut) seed
  have pos:0<d.n := by change 0<x.n;omega
  obtain ⟨f,cf⟩:=form_piece d cut seed pos
  change C=(List.range d.n).filter f at cf
  have dup:C.Nodup := cf ▸ (List.nodup_range.filter _)
  have small {p} (hp:p∈C) : p<d.n := by rw [cf] at hp;exact List.mem_range.mp (List.mem_filter.mp hp).1
  have data : Tables d a M bits words := representedTables x s r h (widthBound (e:ℝ)) u g z a (by omega) prep geo menus az
  have orderedB : (List.range d.n).filter (fun j=>decide (j∈cut))=cut := by
    apply canonicalFilter;rw [←rim];unfold rimOf vertices;rw [List.filter_filter];exact ⟨_,rfl⟩
  have nodup : cut.reverse.Nodup := List.nodup_reverse.mpr (by
    have hh:=List.nodup_range (n:=d.n) |>.filter (fun j=>decide (j∈cut))
    simpa only [orderedB] using hh)
  let revSlot := fun p : ℕ=>q/M^(cut.reverse.idxOf p)%M
  let word := fun j : ℕ=>(a.heap (words+j)).toNat
  let lab := fun p=>word (revSlot p)
  have right (i : ℕ) (hi:i<cut.reverse.length) : revSlot cut.reverse[i]=q/M^i%M := by simp only [revSlot,nodup.idxOf_getElem i hi]
  have rowEq : row=cut.map (fun j=>(j,lab j)) := by
    have acc : decRow M word (fun v j=>decide (1 ≤ a.heap (bits+(v*M+j)))) cut.reverse q=some row := by
      simpa [ordinalAssignment,decRow,word,data.base,data.bitsAt,data.wordsAt] using ok
    have re:=rowLabels M word lab _ cut.reverse q row acc (by intro i hi;exact congrArg word (right i hi))
    simpa using re
  let scratch:=(a.reg 8).toNat
  let cur:=(t.reg 8).toNat
  let idx:=fun p:ℕ=>if p=v then j else revSlot p
  let ext:=(v,word j)::row
  have atMem (p : ℕ) (mem:p∈cut) : t.heap (scratch+p)=(revSlot p:ℤ) := by
    have hh:=List.mem_reverse.mpr mem
    have bound : cut.reverse.idxOf p<cut.reverse.length := List.idxOf_lt_length_iff.mpr hh
    have rv : reverseVertex cut (cut.reverse.idxOf p)=p := by simp [reverseVertex,List.getElem?_eq_getElem bound,List.getElem_idxOf bound]
    have eq:=F.digits (cut.reverse.idxOf p) (by simpa using bound)
    simpa [scratch,rv,revSlot,data.base] using eq
  have sa : (scratch:ℤ)=a.reg 8 := Int.toNat_of_nonneg (by have := menus.cursor;have := az.cursor;omega)
  have res := F.reserved
  have av : scratch+d.n ≤ cur := by change a.reg 8+(d.n:ℤ) ≤ t.reg 8 at res;dsimp [cur];omega
  have curT : (cur:ℤ)=t.reg 8 := Int.toNat_of_nonneg (by omega)
  have jM : j<M := by simpa [data.base] using hj
  have wi (p : ℕ) : idx p<M := by dsimp [idx];split <;> first | exact jM | exact Nat.mod_lt _ data.positive
  obtain ⟨edge,edgePtr,edges⟩:=edge_scene x s r h (widthBound (e:ℝ)) u g z prep geo menus
  have zc:=az.cursor
  have keepZ (p : ℕ) (hp:p<(z.reg 8).toNat) : t.heap p=z.heap p :=
    (F.preserved.tables _ (by dsimp [scratch] at *;omega)).trans (az.tables _ hp)
  have ctrl (p : ℕ) (hp:p=6 ∨ p=7 ∨ (64 ≤ p ∧ p ≤ 81)) := (F.preserved.control p hp).trans (az.control p hp)
  obtain ⟨one,zero,size,_,_,_,_,_,_,_,_,ptrs,_,_,_⟩:=prep
  have asU (p : ℕ) (hp:p=6 ∨ p=7 ∨ (64 ≤ p ∧ p ≤ 81)) : t.reg p=u.reg p :=
    (ctrl p hp).trans ((menus.controls p (by rcases hp with h|h|h <;> omega)).trans (geo.controls p (by rcases hp with h|h|h <;> omega)))
  let W:=WindowProfiles.piece x (r/x.n) (r%x.n)
  let fee:=1000*(M+1)+1000*(d.n+1)^3
  let selected:=fun p=>decide (p∈cut)
  let test:=fun i j=>d.test i j (word (idx i)) (word (idx j))
  have outside:v∉cut := by
    intro yes
    have y: v∈rimOf d C := by rw [show rimOf d C=cut from rim];exact yes
    have hb:=(List.mem_filter.mp y).2;simp [C,hv] at hb
  have extEq : ext=(v::cut).map (fun p=>(p,word (idx p))) := by
    simp only [ext,List.map_cons];congr 1
    · simp [idx]
    · rw [rowEq];apply List.map_congr_left;intro p hp
      have ne:p≠v := fun h=>outside (h ▸ hp)
      simp [lab,idx,ne]
  have eqFlag:=allLabels d v selected (v::cut) (fun p=>word (idx p)) (by
    intro p;simp only [List.mem_cons];constructor
    · intro hit;refine ⟨?_,by simpa [selected,activeOn] using hit⟩
      rcases hit with rfl|pc
      · exact small hv
      · have m:p∈rimOf d C := by rw [show rimOf d C=cut from rim];exact pc
        exact List.mem_range.mp (List.mem_filter.mp (List.mem_filter.mp m).1).1
    · intro hit;simpa [selected,activeOn] using hit.2)
  rw [←extEq] at eqFlag
  obtain ⟨bptr,vec,cb,_,bend,_,bitmap,_⟩:=inp.rows
  have dat : PairData d.n fee v bptr edge scratch s.imem selected idx d.edge test t := by
    refine ⟨(asU 6 (by decide)).trans one,(asU 64 (by decide)).trans size,vert,bp.trans (F.bitmap.trans cb),(ctrl 75 (by decide)).trans edgePtr,sp.trans (F.scratch.trans sa.symm),?_,?_,?_,?_⟩
    · intro p hp;rw [F.preserved.tables _ (by omega),bitmap p hp];simp [bit,selected]
    · intro i hi j hj;obtain ⟨hb,eq⟩:=edges i hi j hj;exact (keepZ _ hb).trans eq
    · intro p hp hit;by_cases yes:p=v
      · simpa [yes,idx,scratch] using wrote
      · exact (atMem p (by simpa [selected] using hit.resolve_left yes)).trans (by simp [idx,yes])
    · intro i hi j hj ci cj w K wh a1 a2 a3 a4
      have fixed (p : ℕ) (pm:p∈localReg) (pc:p=6 ∨ p=7 ∨ (64 ≤ p ∧ p ≤ 81)) := (K p pm).trans (asU p pc)
      have wptr (j : Fin 11) (hm:71+j.val∈localReg) := (fixed _ hm (by have:=j.isLt;omega)).trans (ptrs j)
      have limit:=menus.cursor;change (cursorAt layout 11:ℤ) ≤ z.reg 8 at limit
      have cell (p:ℕ) : word (idx p)=(SingleCodes.words x.n h)[idx p]?.getD 0 := by
        have eq:=(az.tables (words+idx p) (by have high : words+M ≤ cursorAt layout 11 := by simp [words,layout,cursorAt,offsets] <;> omega
                                              have := wi p;omega)).trans (menus.words _ (wi p))
        simp [word,eq,h]
      obtain ⟨o,k,run,kt,flag,oh,oo,oc⟩:=regional_compatibility_from_tables x.n h s.imem W ⟨i,hi⟩ ⟨j,hj⟩ (idx i) (idx j) g z w menus
        (wi i) (wi j) ((fixed 6 (by decide) (by decide)).trans one) ((fixed 64 (by decide) (by decide)).trans size)
        ((K 70 (by decide)).trans ((F.preserved.control 70 (by decide)).trans data.base)) a1 a2 a3 a4
        (wptr ⟨6,by decide⟩ (by decide)) (wptr ⟨8,by decide⟩ (by decide)) (wptr ⟨9,by decide⟩ (by decide))
        (by intro p hp;rw [wh];exact keepZ _ (by change p<cursorAt layout 11 at hp;omega))
      have piece : Bits.piece x.n x.mem (r/x.n) (r%x.n)=WindowProfiles.piece x (r/x.n) (r%x.n) := rfl
      exact ⟨o,k,run,kt,by simpa [test,bit,cell,d,integerData,arrange,W,piece] using flag,oh,oc,oo⟩
  let a':=(t.assign 984 1).assign 233 1
  have init : Logical.Executes d.n s.imem (chain initLocal) t a' 5 := by apply evalLine_sound;rfl
  obtain ⟨b',k,scan,tm,flag,heap,cl,out⟩:=outerAll (dat.move (unchanged init (by decide)) rfl) (by simp [a',Logical.State.assign])
  have reg (r : ℕ) (h:writesReg r outerLoop=false) (h':writesReg r (chain initLocal)=false) :=
    (scan.preserves r h).trans (init.preserves r h')
  have flagB : b'.reg 233=if localOK d ext then 1 else 0 := by rw [flag];exact congrArg bit eqFlag
  have bCnt : b'.reg 82=(b'.output.length:ℤ) := by rw [out,reg 82 (by decide) (by decide)];exact F.preserved.count
  obtain ⟨y,l,finish,bt,hy,cy,ct,oy⟩:=write_trial_close_record d.n scratch v s.imem b' (localOK d ext)
    ((reg 6 (by decide) (by decide)).trans dat.one) ((reg 64 (by decide) (by decide)).trans dat.size)
    ((reg 225 (by decide) (by decide)).trans dat.tabAt) ((reg 226 (by decide) (by decide)).trans vert) flagB
    (cl.trans F.preserved.available) bCnt
  obtain ⟨cc,prc,eq⟩:=splitChain initLocal init
  have whole : Logical.Executes d.n s.imem (chain ((listOf src_trial).drop 10)) t y (cc+(1+k+l)) :=
    prc.continue _ (.seq scan finish)
  have preserve (r : ℕ) (p : r=6 ∨ r=7 ∨ r=8 ∨ (64 ≤ r ∧ r ≤ 81) ∨ r∈[241,242,243,247,250]) :=
    whole.preserves r (closeFrameReg r p)
  have new : TrialFrame d.n cut q a y := by
    refine ⟨⟨⟨?_,?_,?_,ct,cy⟩,?_,?_,?_,?_,?_,?_⟩,?_⟩
    · intro r hr;exact (preserve r (by rcases hr with h|h|h <;> omega)).trans (F.preserved.control r hr)
    · rw [preserve 8 (by decide)];exact F.preserved.cursor
    · intro p hp;rw [hy,if_neg (by change p<scratch at hp;omega),heap];exact F.preserved.tables _ hp
    · exact (preserve 241 (by decide)).trans F.bitmap
    · exact (preserve 242 (by decide)).trans F.vector
    · exact (preserve 243 (by decide)).trans F.lengthReg
    · exact (preserve 247 (by decide)).trans F.component
    · exact (preserve 250 (by decide)).trans F.scratch
    · rw [preserve 8 (by decide)];exact F.reserved
    · intro i hi
      have ir : i<cut.reverse.length := by simpa using hi
      have incl : reverseVertex cut i∈cut := List.mem_reverse.mp (by simpa [reverseVertex,List.getElem?_eq_getElem ir] using List.getElem_mem ir)
      have ne : reverseVertex cut i≠v := fun h=>outside (h ▸ incl)
      change y.heap (scratch+reverseVertex cut i)=_;rw [hy,if_neg (by omega),heap];exact F.digits i hi
  refine ⟨y,_,whole,?_,new,?_⟩
  · have bound:=localCost x.n x.cap e (by omega) (by dsimp [World.cap];omega) ep el
    change k ≤ 9+x.n*(130+x.n*(1000*(M+1)+1000*(x.n+1)^3+415+6*x.n)) at tm
    change l ≤ 300+x.n*(165+6*x.n) at bt
    exact (show cc+(1+k+l) ≤ 5+(9+x.n*(130+x.n*(1000*(M+1)+1000*(x.n+1)^3+415+6*x.n)))+(300+x.n*(165+6*x.n)) by omega).trans bound
  · rw [oy,out];simp [a',ext,word,data.wordsAt,Logical.State.assign]

#print axioms solution
