-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.execute_one_vertex_trial
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:48:50.461399+00:00
-- url     : https://prove2.me/submissions/7929b5b6-4e32-4214-9e8a-34d15554da74

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_emit_canonical_owned_literals
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_prepare_trial_child_component
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_emit_trial_children_and_local_test
import Definitions.Def_StableMSR_TrialChildren
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

private abbrev startRegs (r : ℕ) := r≤81 ∨ r∈[223,224,225,226,227,241,242,243,247,250]
private lemma litFrameReg (r : ℕ) (hr : startRegs r) : writesReg r (chain ((listOf src_trial).take 5))=false := by
  rcases hr with sm|other
  · have all : ∀i:Fin 82,writesReg i.val (chain ((listOf src_trial).take 5))=false := by decide
    exact all ⟨r,by omega⟩
  · simp at other
    rcases other with h|h|h|h|h|h|h|h|h|h <;> subst r <;> decide
private lemma delFrameReg (r : ℕ) (hr : startRegs r ∨ r=82) (safe:r≠8) :
    writesReg r (chain (((listOf src_trial).drop 5).take 4))=false := by
  rcases hr with (sm|other)|rfl
  · have all : ∀i:Fin 82,i.val≠8 → writesReg i.val (chain (((listOf src_trial).drop 5).take 4))=false := by decide
    exact all ⟨r,by omega⟩ safe
  · simp at other
    rcases other with h|h|h|h|h|h|h|h|h|h <;> subst r <;> decide
  · decide

private lemma trialEstimate (n cap c D b : ℕ) (e : ℚ) (hn : 2≤n) (hc : n+1≤cap) (ep : 0<e) (el : e<1) :
    let M:=sizes n (budget (e:ℝ))
    let E:=parameterEnvelope (e:ℝ)
    500*(M+1)+500*(n+1)^4+(200+300*n)+c*cap^D*n^(b*E) ≤ (2000+c)*cap^(D+4)*n^((b+15)*E) := by
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
  let B:=cap^4*P*F
  have cp : 1≤cap := by omega
  have pp : 1≤P := Nat.mul_pos (Nat.pow_pos cp) (Nat.pow_pos (by omega))
  have fp : 1≤F := Nat.pow_pos (by omega)
  have cap4 : 1≤cap^4 := Nat.pow_pos cp
  have bf : F≤B := by
    calc F=1*F := by simp
         _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_pos cap4 pp)
  have p4 : (n+1)^4≤B := by
    calc (n+1)^4=(n+1)^4*1*1 := by simp
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hc 4) pp) fp
  have bp : P≤B := by
    calc P=1*P*1 := by simp
         _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul cap4 (le_refl P)) fp
  have nBound : n≤B := by
    have small : (n+1)^1≤(n+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
    simp only [pow_one] at small;omega
  have cb : c*P≤c*B := Nat.mul_le_mul_left _ bp
  change 500*(M+1)+500*(n+1)^4+(200+300*n)+c*cap^D*n^(b*E) ≤ _
  rw [Nat.mul_assoc c]
  change 500*(M+1)+500*(n+1)^4+(200+300*n)+c*P ≤ _
  calc _ ≤ 2000*B+c*B := by omega
       _ = _ := by dsimp [B,P,F];rw [show (b+15)*E=b*E+15*E by ring,pow_add n,pow_add cap D 4];ring

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
      Scene.CutTraversal.VertexTrials d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ))) := by
  obtain ⟨c,D,b,calls⟩:=Root.emit_trial_children_and_local_test
  refine ⟨2000+c,D+4,b+15,?_⟩
  intro e ep el x s hk hkn ready bounded r p pr pp rr key u prep g geo z menus level hl
  let h:=budget (e:ℝ)
  let M:=sizes x.n h
  let layout:=offsets x.n M
  let d:=integerData x.n x.mem s.imem r h
  let W:=WindowProfiles.piece x (r/x.n) (r%x.n)
  let E:=parameterEnvelope (e:ℝ)
  have steps:=calls e ep el x s hk hkn ready bounded r p pr pp rr key u prep g geo z menus level hl
  change VertexTrials d _ level s.imem z ((2000+c)*x.cap^(D+4)*x.n^((b+15)*E))
  intro a cut seed az hc inp hs rs
  dsimp only
  intro hd carg len rim q hq row ok v hv j hj allowedWord t F cp0 bp0 sp0 vert slot
  let C:=pieceAt d (allowed d cut) seed
  change v∈C at hv
  have pos : 0<d.n := by change 0<x.n;omega
  obtain ⟨f,eqC⟩:=form_piece d cut seed pos
  have hvn : v<x.n := by
    change v∈pieceAt d (allowed d cut) seed at hv
    rw [eqC] at hv;exact List.mem_range.mp (List.mem_filter.mp hv).1
  have outside : v∉cut := by
    intro inside
    rw [←rim] at inside
    have no:=(List.mem_filter.mp inside).2
    simp [hv,C] at no
  obtain ⟨one,zero,size,_,_,_,_,_,base,_,_,pointers,_,_,_⟩:=prep
  have ca (j : ℕ) (hj:j=6 ∨ j=7 ∨ (64≤j ∧ j≤81)) : a.reg j=u.reg j :=
    (az.control j hj).trans ((menus.controls j (by rcases hj with h|h|h <;> omega)).trans
      (geo.controls j (by rcases hj with h|h|h <;> omega)))
  have ct (j : ℕ) (hj:j=6 ∨ j=7 ∨ (64≤j ∧ j≤81)) : t.reg j=u.reg j := (F.preserved.control j hj).trans (ca j hj)
  have ab : a.reg 70=(M:ℤ) := (ca 70 (by decide)).trans base
  have aptr (j : Fin 11) : a.reg (71+j.val)=(cursorAt layout j.val:ℤ) := (ca _ (by have:=j.isLt;omega)).trans (pointers j)
  have tptr (j : Fin 11) : t.reg (71+j.val)=(cursorAt layout j.val:ℤ) := (ct _ (by have:=j.isLt;omega)).trans (pointers j)
  have safe : (cursorAt layout 11:ℤ)≤z.reg 8 := menus.cursor
  have nc := az.cursor
  have nonneg : 0≤a.reg 8 := by omega
  let scratch := (a.reg 8).toNat
  let dst := (t.reg 8).toNat
  have sa : (scratch:ℤ)=a.reg 8 := Int.toNat_of_nonneg nonneg
  have sp : (t.reg 250)=(scratch:ℤ) := F.scratch.trans sa.symm
  have reserve := F.reserved
  have avail : scratch+x.n≤dst := by change a.reg 8 + (x.n:ℤ) ≤ t.reg 8 at reserve; dsimp [scratch,dst];omega
  have dc : (dst:ℤ)=t.reg 8 := Int.toNat_of_nonneg (by omega)
  have tabA (i : ℕ) (hi:i<cursorAt layout 11) := az.tables i (by omega)
  have tabT (i : ℕ) (hi:i<cursorAt layout 11) : t.heap i=z.heap i := (F.preserved.tables i (by omega)).trans (tabA i hi)
  have hword : j<M := by simpa [ab] using hj
  let ix:=v*M+j
  have ixlt : ix<x.n*M := by
    calc v*M+j < v*M+M := Nat.add_lt_add_left hword _
         _ = (v+1)*M := (Nat.succ_mul _ _).symm
         _ ≤ _ := Nat.mul_le_mul_right _ hvn
  have we : cursorAt layout 5+M≤cursorAt layout 11 := by simp [layout,cursorAt,offsets] <;> omega
  have be : cursorAt layout 10+x.n*M≤cursorAt layout 11 := by simp [layout,cursorAt,offsets] <;> omega
  have permitted : 1 ≤ t.heap (cursorAt layout 10+ix) := by
    rw [F.preserved.tables _ (by omega)]
    have p81 : a.reg 81=(cursorAt layout 10:ℤ) := aptr ⟨10,by decide⟩
    simpa only [p81,ab,Int.toNat_natCast,ix] using allowedWord
  let label := (a.heap ((a.reg 76).toNat+j)).toNat
  have codeEq : label=(SingleCodes.words x.n h)[j]?.getD 0 := by
    dsimp only [label]
    have ptr : a.reg 76=(cursorAt layout 5:ℤ) := aptr ⟨5,by decide⟩
    rw [ptr,Int.toNat_natCast,tabA _ (by omega),menus.words j hword,Int.toNat_natCast]
  obtain ⟨y,l,wr,tl,heapY,openY,countY,outY⟩:=emit_canonical_owned_literals s.imem W h ⟨v,hvn⟩ j u g z t geo menus hword permitted
    ((ct 6 (by decide)).trans one) ((ct 64 (by decide)).trans size) ((ct 70 (by decide)).trans base)
    vert slot (tptr ⟨1,by decide⟩) (tptr ⟨6,by decide⟩) (tptr ⟨7,by decide⟩) (tptr ⟨9,by decide⟩)
    F.preserved.available F.preserved.count tabT
  have outL : y.output=t.output++(d.owned v label).map Instr.lit := by rw [codeEq];exact outY
  have keepY (j : ℕ) (hj:startRegs j) : y.reg j=t.reg j := wr.preserves j (litFrameReg j hj)
  obtain ⟨cp,cpA,cpEnd,cbits⟩:=carg.row
  have ycp : y.reg 223=(cp:ℤ) := (keepY 223 (by decide)).trans (cp0.trans (F.component.trans cpA))
  have ysp : y.reg 225=(scratch:ℤ) := (keepY 225 (by decide)).trans (sp0.trans sp)
  obtain ⟨w,k,rm,tk,newptr,cursor,ow,cw,hw⟩:=prepare_trial_child_component x.n v j cp scratch dst s.imem y
    (fun p=>decide (p∈C)) hvn cpEnd avail ((keepY 6 (by decide)).trans ((ct 6 (by decide)).trans one))
    ((keepY 7 (by decide)).trans ((ct 7 (by decide)).trans zero)) ((keepY 64 (by decide)).trans ((ct 64 (by decide)).trans size))
    ((keepY 8 (by decide)).trans dc.symm) ycp ysp ((keepY 226 (by decide)).trans vert) ((keepY 227 (by decide)).trans slot)
    (by intro i hi;rw [heapY,F.preserved.tables _ (by change cp+x.n ≤ scratch at cpEnd;dsimp [scratch] at cpEnd;omega)]
        simpa only [decide_eq_true_eq] using cbits i hi)
  have keepW (j : ℕ) (hj:startRegs j) (no:j≠8) : w.reg j=t.reg j :=
    (rm.preserves j (delFrameReg j (.inl hj) no)).trans (keepY j hj)
  have old (p : ℕ) (hp:p<scratch) : w.heap p=a.heap p := by
    rw [hw,if_neg (by omega),if_neg (by omega),heapY];exact F.preserved.tables p hp
  have countW : w.reg 82=(w.output.length:ℤ) := by rw [ow,rm.preserves 82 (delFrameReg 82 (.inr rfl) (by decide)),countY]
  have fw : TrialFrame d.n cut q a w := by
    refine ⟨⟨⟨?_,?_,old,countW,cw.trans openY⟩,?_,?_,?_,?_,?_,?_⟩,?_⟩
    · intro r hr;rw [keepW r (by unfold startRegs;left;rcases hr with h|h|h <;> omega) (by rcases hr with h|h|h <;> omega)];exact F.preserved.control r hr
    · rw [cursor,←sa];exact_mod_cast (show scratch≤dst+x.n by omega)
    · exact (keepW 241 (by decide) (by decide)).trans F.bitmap
    · exact (keepW 242 (by decide) (by decide)).trans F.vector
    · exact (keepW 243 (by decide) (by decide)).trans F.lengthReg
    · exact (keepW 247 (by decide) (by decide)).trans F.component
    · exact (keepW 250 (by decide) (by decide)).trans F.scratch
    · change a.reg 8+(x.n:ℤ)≤w.reg 8;rw [cursor,←sa];exact_mod_cast (show scratch+x.n≤dst+x.n by omega)
    · intro i hi
      let p:=reverseVertex cut i
      have pm : p∈cut := by
        have ir : i<cut.reverse.length := by simpa using hi
        exact List.mem_reverse.mp (by simpa [p,reverseVertex,List.getElem?_eq_getElem ir] using List.getElem_mem ir)
      have pc : p∈rimOf d C := rim.symm ▸ pm
      have pn : p<x.n := List.mem_range.mp (List.mem_filter.mp (List.mem_filter.mp pc).1).1
      have ne : p≠v := fun h=>outside (h ▸ pm)
      change w.heap (scratch+p)=_
      rw [hw,if_neg (by omega),if_neg (by omega),heapY];exact F.digits i hi
  have out:=steps a cut seed az hc inp hs rs hd carg len rim q hq row ok v hv j hj allowedWord w fw
    (by rw [keepW 223 (by decide) (by decide),keepW 247 (by decide) (by decide),cp0])
    (by rw [keepW 224 (by decide) (by decide),keepW 241 (by decide) (by decide),bp0])
    (by rw [keepW 225 (by decide) (by decide),keepW 250 (by decide) (by decide),sp0])
    ((keepW 226 (by decide) (by decide)).trans vert) ((keepW 227 (by decide) (by decide)).trans slot)
    dst newptr (by rw [cursor,Int.toNat_natCast];rfl) (by
        intro p hp;change p<x.n at hp
        change w.heap (dst+p)=(if p∈C ∧ p≠v then 1 else 0)
        rw [hw,if_pos (by omega)];simp)
    (by change w.heap (scratch+v)=_;rw [hw,if_neg (by omega),if_pos rfl])
  obtain ⟨last,zCost,tail,cost,frame,output⟩:=out
  obtain ⟨sl,left,slEq⟩:=splitChain ((listOf src_trial).take 5) wr
  obtain ⟨sd,mid,sdEq⟩:=splitChain (((listOf src_trial).drop 5).take 4) rm
  refine ⟨last,_,left.continue _ (mid.continue _ tail),?_,frame,?_⟩
  · have bound:=trialEstimate x.n x.cap c D b e (by omega) (by dsimp [World.cap];omega) ep el
    change zCost≤c*x.cap^D*x.n^(b*E) at cost
    change l≤500*(M+1)+500*(x.n+1)^4 at tl
    change 500*(M+1)+500*(x.n+1)^4+(200+300*x.n)+c*x.cap^D*x.n^(b*E) ≤ _ at bound
    exact (show sl+(sd+zCost)≤500*(M+1)+500*(x.n+1)^4+(200+300*x.n)+c*x.cap^D*x.n^(b*E) by omega).trans bound
  · rw [output,ow,outL];simp only [trial,List.append_assoc,label] <;> rfl

#print axioms solution
