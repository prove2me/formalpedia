-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.emit_trial_children_and_local_test
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:53:54.243874+00:00
-- url     : https://prove2.me/submissions/4b6209e8-7e28-4efe-b88f-f2ec094c954c

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_close_trial_with_local_consistency
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_scan_distinct_trial_children
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_child_boundary_after_deleting_vertex
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
open Scene.SeparatorLevels TightLanguage SingleCircuit
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
    by dsimp [M,sizes]; positivity,by change cursorAt layout 5+M≤_;omega,by change cursorAt layout 10+x.n*M≤_;omega,?_,?_⟩
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

private lemma sweepEstimate (n cap c D b : ℕ) (e : ℚ) (hn : 2≤n) (hc : n+1≤cap) (ep : 0<e) (el : e<1) :
    let M:=sizes n (budget (e:ℝ))
    let E:=parameterEnvelope (e:ℝ)
    (1+(9+n*(1600*(n+1)^4+700*(n+1)*(n+M+1)+505)))+c*cap^D*n^(b*E) ≤ (10000+c)*cap^(D+5)*n^((b+15)*E) := by
  let O := ownerBound (e:ℝ)
  let E := parameterEnvelope (e:ℝ)
  let W := widthBound (e:ℝ)
  let H := budget (e:ℝ)+1
  let M := sizes n (budget (e:ℝ))
  let F := n^(15*E)
  let P := cap^D*n^(b*E)
  have er : (0:ℝ)<e := by exact_mod_cast ep
  have er' : (e:ℝ)<1 := by exact_mod_cast el
  have op : 1 ≤ O := by
    unfold O ownerBound; apply Nat.le_floor; rw [le_div_iff₀ er]; norm_num; linarith
  have hH : H ≤ 5*O := by dsimp [H,budget,O] at *; omega
  have OW : O*(W+1) ≤ E := by dsimp [O,W,E,parameterEnvelope]; omega
  have O1 : O ≤ E := (by simpa using Nat.mul_le_mul_left O (show 1≤W+1 by omega) : O ≤ O*(W+1)).trans OW
  have Hn : H ≤ n^H := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left hn _)
  have M0 : M ≤ n^(3*H) := by
    change H*n^(2*H) ≤ _
    calc H*n^(2*H) ≤ n^H*n^(2*H) := Nat.mul_le_mul_right _ Hn
         _ = _ := by rw [← pow_add]; congr 1; omega
  have MF : M ≤ F := M0.trans (Nat.pow_le_pow_right (by omega) (by omega))
  let B:=cap^5*P*F
  have cp : 1≤cap := by omega
  have pp : 1≤P := Nat.mul_pos (Nat.pow_pos cp) (Nat.pow_pos (by omega))
  have fp : 1≤F := Nat.pow_pos (by omega)
  have pow : (n+1)^5 ≤ cap^5 := Nat.pow_le_pow_left hc _
  have big : (n+1)^5*(M+1) ≤ 2*B := by
    have m : M+1≤F*2 := by omega
    have z := Nat.mul_le_mul (Nat.mul_le_mul pow pp) m
    simp only [Nat.mul_one] at z
    calc (n+1)^5*(M+1) ≤ cap^5*P*(F*2) := z
         _ = 2*B := by dsimp [B];ring
  have taper : 1+(9+n*(1600*(n+1)^4+700*(n+1)*(n+M+1)+505)) ≤ 5000*((n+1)^5*(M+1)) := by ring_nf;omega
  have bp : P≤B := by
    calc P=1*P*1 := by simp
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_pos cp) (le_refl P)) fp
  have cb:=Nat.mul_le_mul_left c bp
  dsimp only
  change 1+(9+n*(1600*(n+1)^4+700*(n+1)*(n+M+1)+505))+c*cap^D*n^(b*E) ≤ _
  rw [Nat.mul_assoc c]
  calc _ ≤ 10000*B+c*B := by change _+c*P≤_;omega
       _ = _ := by dsimp [B,P,F];rw [show (b+15)*E=b*E+15*E by ring,pow_add n,pow_add cap D 5];ring
private lemma mapValue (xs : List ℕ) (f : ℕ→ℕ) (p : ℕ) (hp:p∈xs) : value (xs.map (fun j=>(j,f j))) p=f p := by
  induction xs with
  | nil=>simp at hp
  | cons x xs ih=>
    by_cases eq:x=p
    · simp [value,eq]
    · have mem:p∈xs := (List.mem_cons.mp hp).resolve_left (Ne.symm eq)
      simpa [value,eq] using ih mem
private lemma sweepReg (r : ℕ) (hr : r=6 ∨ r=7 ∨ (64≤r ∧ r≤81) ∨ r∈[223,224,225,226,227,241,242,243,247,250]) :
    writesReg r (Scene.BlockRows.instruction src_trial 9)=false := by
  rcases hr with rfl|rfl|small|hs
  · decide
  · decide
  · have all : ∀i:Fin 82,64 ≤ i.val → writesReg i.val (Scene.BlockRows.instruction src_trial 9)=false := by decide
    exact all ⟨r,by omega⟩ small.1
  · simp at hs
    rcases hs with h|h|h|h|h|h|h|h|h|h <;> subst r <;> decide

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
      Scene.CutTraversal.ChildTrials d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ))) := by
  obtain ⟨c,D,b,calls⟩:=Root.close_trial_with_local_consistency
  refine ⟨10000+c,D+5,b+15,?_⟩
  intro e ep el x s hk hkn ready bounded r p pr pp rr key u prep g geo z menus level hl
  let h:=budget (e:ℝ)
  let M:=sizes x.n h
  let layout:=offsets x.n M
  let bits:=cursorAt layout 10
  let words:=cursorAt layout 5
  let d:=integerData x.n x.mem s.imem r h
  let E:=parameterEnvelope (e:ℝ)
  have tail:=calls e ep el x s hk hkn ready bounded r p pr pp rr key u prep g geo z menus level hl
  change ChildTrials d _ level s.imem z _
  intro a cut seed az hc inp hs rs
  dsimp only
  intro hd carg len rim q hq row ok v hv j hj permitted t F cp bp sp vert slot dst ptr limit mask wrote
  let C:=pieceAt d (allowed d cut) seed
  have pos:0<d.n := by change 0<x.n;omega
  obtain ⟨f,cf⟩:=form_piece d cut seed pos
  change C=(List.range d.n).filter f at cf
  have dup:C.Nodup := cf ▸ (List.nodup_range.filter _)
  have small {p} (hp:p∈C) : p<d.n := by rw [cf] at hp;exact List.mem_range.mp (List.mem_filter.mp hp).1
  let mark:=fun p=>decide (p∈C ∧ p≠v)
  have maskEq : (List.range d.n).filter mark=C.erase v := by
    rw [dup.erase_eq_filter]
    have canonical:=canonicalFilter (xs:=C) ⟨f,cf⟩
    rw [←canonical,List.filter_filter];apply List.filter_congr;intro p _
    by_cases mem:p∈C <;> by_cases eq:p=v <;> simp [mark,canonical,mem,eq]
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
  have av : scratch+d.n≤cur := by change a.reg 8+(d.n:ℤ)≤t.reg 8 at res;dsimp [cur];omega
  have curT : (cur:ℤ)=t.reg 8 := Int.toNat_of_nonneg (by omega)
  have jM : j<M := by simpa [data.base] using hj
  have wi (p : ℕ) : idx p<M := by dsimp [idx];split <;> first | exact jM | exact Nat.mod_lt _ data.positive
  have pword : ∀p,p=v ∨ p∈cut → value ext p=word (idx p) := by
    intro p mem;by_cases e:p=v
    · simp [ext,value,idx,e]
    · have pc:=mem.resolve_left e
      have eq : value row p=lab p := rowEq ▸ mapValue cut lab p pc
      simpa [ext,idx,value,Ne.symm e,e,lab] using eq
  have cap : C.toFinset.card≤d.n := by rw [List.toFinset_card_of_nodup dup,cf];exact (List.length_filter_le _ _).trans (by simp)
  have dig (i : ℕ) (hi:i∈(List.range d.n).filter mark) (p : ℕ) (hp:p∈rimOf d (pieceAt d ((List.range d.n).filter mark) i)) :
      scratch+p<cur ∧ t.heap (scratch+p)=(idx p:ℤ) ∧ words+idx p<cur ∧ t.heap (words+idx p)=(value ext p:ℤ) ∧ value ext p≤M := by
    rw [maskEq] at hi hp
    have mem : p=v ∨ p∈cut := by rw [←rim];exact child_boundary_after_deleting_vertex d C v i cap hi p hp
    have pn : p<d.n := List.mem_range.mp (List.mem_filter.mp (List.mem_filter.mp hp).1).1
    have lim:=data.wordEnd;have il:=wi p;have val:=data.values (idx p) il
    refine ⟨by omega,?_,by omega,?_,?_⟩
    · by_cases yes:p=v
      · simpa [yes,idx,scratch] using wrote
      · simpa [idx,yes] using atMem p (mem.resolve_left yes)
    · rw [pword p mem,F.preserved.tables _ (by omega)];exact (Int.toNat_of_nonneg val.1).symm
    · rw [pword p mem];exact val.2
  obtain ⟨edge,edgePtr,edges⟩:=edge_scene x s r h (widthBound (e:ℝ)) u g z prep geo menus
  have zc:=az.cursor
  have keepZ (p : ℕ) (hp:p<(z.reg 8).toNat) : t.heap p=z.heap p :=
    (F.preserved.tables _ (by dsimp [scratch] at *;omega)).trans (az.tables _ hp)
  have ctrl (p : ℕ) (hp:p=6 ∨ p=7 ∨ (64≤p ∧ p≤81)) := (F.preserved.control p hp).trans (az.control p hp)
  obtain ⟨one,zero,size,_,_,_,_,_,_,_,_,ptrs,_,_,_⟩:=prep
  have asU (p : ℕ) (hp:p=6 ∨ p=7 ∨ (64≤p ∧ p≤81)) : t.reg p=u.reg p :=
    (ctrl p hp).trans ((menus.controls p (by rcases hp with h|h|h <;> omega)).trans (geo.controls p (by rcases hp with h|h|h <;> omega)))
  obtain ⟨y,k,scan,bt,cursor,heap,cl,count,out⟩:=scan_distinct_trial_children d cur dst 0 edge scratch words M s.imem t mark ext idx
    ((asU 6 (by decide)).trans one) ((asU 7 (by decide)).trans zero) ((asU 64 (by decide)).trans size) curT.symm ptr
    ((asU 71 (by decide)).trans (ptrs ⟨0,by decide⟩)) ((ctrl 75 (by decide)).trans edgePtr)
    (sp.trans (F.scratch.trans sa.symm)) ((F.preserved.control 76 (by decide)).trans data.wordsAt)
    F.preserved.available F.preserved.count
    (by intro p hp;exact ⟨by omega,by simpa [mark] using mask p hp⟩)
    (by intro p hp;change p<x.n at hp
        have small : x.n≤cursorAt layout 5 := by simp [layout,cursorAt,offsets] <;> omega
        have higher : cursorAt layout 5≤cursorAt layout 11 := by simp [layout,cursorAt,offsets] <;> omega
        have endZ:=menus.cursor;change (cursorAt layout 11:ℤ)≤z.reg 8 at endZ
        simp only [Nat.zero_add];refine ⟨by omega,?_⟩
        rw [keepZ _ (by omega),menus.geometry _ (by change p<cursorAt layout 5;omega)]
        have region : Bits.piece x.n x.mem (r/x.n) (r%x.n)=WindowProfiles.piece x (r/x.n) (r%x.n) := rfl
        simpa [d,integerData,arrange,Bits.normalized,Bits.lookup,hp,cursorAt,region] using geo.active ⟨p,hp⟩)
    (by intro q hq p hp;obtain ⟨hb,eq⟩:=edges q hq p hp;change edge+(q*d.n+p)<(z.reg 8).toNat at hb
        refine ⟨by omega,(keepZ _ hb).trans eq⟩) dig
  have reg (r : ℕ) (hr : r=6 ∨ r=7 ∨ (64≤r ∧ r≤81) ∨ r∈[223,224,225,226,227,241,242,243,247,250]) := scan.preserves r (sweepReg r hr)
  have fr : TrialFrame d.n cut q a y := by
    refine ⟨⟨⟨?_,F.preserved.cursor.trans cursor,?_,count,cl⟩,?_,?_,?_,?_,?_,F.reserved.trans cursor⟩,?_⟩
    · intro r hr;exact (reg r (by rcases hr with h|h|h <;> omega)).trans (F.preserved.control r hr)
    · intro p hp;exact (heap _ (by change p<scratch at hp;omega)).trans (F.preserved.tables p hp)
    · exact (reg 241 (by decide)).trans F.bitmap
    · exact (reg 242 (by decide)).trans F.vector
    · exact (reg 243 (by decide)).trans F.lengthReg
    · exact (reg 247 (by decide)).trans F.component
    · exact (reg 250 (by decide)).trans F.scratch
    · intro i hi
      have ir : i<cut.reverse.length := by simpa using hi
      have incl : reverseVertex cut i∈cut := List.mem_reverse.mp (by simpa [reverseVertex,List.getElem?_eq_getElem ir] using List.getElem_mem ir)
      have mem : reverseVertex cut i∈rimOf d C := by rw [show rimOf d C=cut from rim];exact incl
      have small : reverseVertex cut i<d.n := List.mem_range.mp (List.mem_filter.mp (List.mem_filter.mp mem).1).1
      exact (heap _ (by change scratch+_<cur;omega)).trans (F.digits i hi)
  obtain ⟨last,l,finish,cost,frame,o⟩:=tail a cut seed az hc inp hs rs hd carg len rim q hq row ok v hv j hj permitted y fr
    (by rw [reg 223 (by decide),reg 247 (by decide),cp])
    (by rw [reg 224 (by decide),reg 241 (by decide),bp])
    (by rw [reg 225 (by decide),reg 250 (by decide),sp])
    ((reg 226 (by decide)).trans vert) ((reg 227 (by decide)).trans slot) ((heap _ (by have := small hv;change scratch+v<cur;omega)).trans wrote)
  refine ⟨last,_,.seq scan finish,?_,frame,?_⟩
  · have bound:=sweepEstimate x.n x.cap c D b e (by omega) (by dsimp [World.cap];omega) ep el
    change k ≤ 9+x.n*(1600*(x.n+1)^4+700*(x.n+1)*(x.n+M+1)+505) at bt
    change l≤c*x.cap^D*x.n^(b*E) at cost
    exact (Nat.add_le_add (Nat.add_le_add_left bt 1) cost).trans bound
  · rw [o,out,maskEq];simp [children,ext,word,data.wordsAt,List.map_map,List.append_assoc,Function.comp_def] <;> exact ⟨rfl,rfl⟩

#print axioms solution
