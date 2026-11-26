-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.write_eligible_component_entries
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T00:54:30.107425+00:00
-- url     : https://prove2.me/submissions/eee1aebe-b004-4c32-9fcd-cfcb7d7dd28f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_boundary_assignments_in_ordinal_order
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_write_one_boundary_ordinal
import Definitions.Def_StableMSR_SeparatorOrdinals
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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.TightLanguage SeparatorLevels
set_option maxRecDepth 50000
set_option maxHeartbeats 7000000

private def powerBody : Program := chain [.op (.multiply 1079 249 70),.op (.regular (.copy 249 1079))]
private lemma entryCode : entryProgram = chain [
    .op (.regular (.set 1076 1)), .op (.regular (.copy 249 1076)),
    forCount 245 1078 243 powerBody, .op (.alloc 1082 64), .op (.regular (.copy 250 1082)),
    forCount 251 1085 249 ordinalBody] := rfl

private structure PowState (a t : State) (M i : ℕ) : Prop where
  accum : t.reg 249 = ((M^i : ℕ):ℤ)
  regs : ∀ j, j ∉ [1076,249,245,1078,1079] → t.reg j = a.reg j
  heap : t.heap = a.heap
  output : t.output = a.output
  closed : t.closed = a.closed

private lemma powIndex {a t M i j v} (H : PowState a t M i) (hj : j=245 ∨ j=1078) :
    PowState a (t.assign j v) M i := by
  rcases hj with rfl|rfl <;> constructor <;> try assumption
  all_goals first
    | simpa [State.assign] using H.accum
    | intro j hj; have := H.regs j hj; simp at hj; simpa [State.assign, hj] using this
    | exact H.heap
    | exact H.output
    | exact H.closed

private lemma runPower {n : ℕ} {m : ℤ→ℤ} (a : State) (M L : ℕ)
    (one : a.reg 6=1) (base : a.reg 70=(M:ℤ)) (len : a.reg 243=(L:ℤ)) :
    let s := (a.assign 1076 1).assign 249 1
    ∃ t k, Executes n m (forCount 245 1078 243 powerBody) s t k ∧
      k ≤ 9+L*(30+6*M) ∧ PowState a t M L := by
  let s := (a.assign 1076 1).assign 249 1
  have start : PowState a s M 0 := by
    refine ⟨by simp [s,State.assign],?_,rfl,rfl,rfl⟩
    intro j hj; simp at hj; simp [s,State.assign,hj]
  apply (fun ⟨t,k,ex,bnd,H⟩ => ⟨t,k,ex,by simpa only [show 25+6*M+5=30+6*M by omega] using bnd,H⟩ :
    (∃ t k, Executes n m (forCount 245 1078 243 powerBody) s t k ∧ k ≤ 9+L*((25+6*M)+5) ∧ PowState a t M L) → _)
  apply source_for 245 1078 243 L (25+6*M) powerBody (fun i t => PowState a t M i) (by decide) (by decide)
    s (by simpa [s,State.assign] using len)
  · exact powIndex (powIndex (powIndex start (.inl rfl)) (.inr rfl)) (.inr rfl)
  · intro i hi t H idx last
    have h1 := (H.regs 6 (by decide)).trans one
    have hM := (H.regs 70 (by decide)).trans base
    let u := t.assign 1079 (t.reg 249*t.reg 70)
    let v := u.assign 249 (u.reg 1079)
    have mul : (Operation.multiply 1079 249 70).next n m t = some (u,8+6*M) := by
      simp [Operation.next,u,h1,H.accum,hM]
    have run : Executes n m powerBody t v (1+(8+6*M)+(1+1+1)) :=
      .seq (.op mul) (.seq (.op rfl) (.skip _))
    have nxt : PowState a v M (i+1) := by
      refine ⟨?_,?_,H.heap,H.output,H.closed⟩
      · simp [v,u,State.assign,H.accum,hM,pow_succ]
      · intro j hj; have hr := H.regs j hj; simp at hj; simpa [v,u,State.assign,hj] using hr
    exact ⟨v,_,run,by omega,by simp [v,u,State.assign],by simp [v,u,State.assign],powIndex nxt (.inl rfl)⟩

private lemma frameIndex {n a t j val} (h : OrdinalFrame n a t) (hj : j=251 ∨ j=1085) :
    OrdinalFrame n a (t.assign j val) := by
  have reg (r : ℕ) (hr : r ≠ j) : (t.assign j val).reg r=t.reg r := by simp [State.assign,hr]
  have far (r : ℕ) (h : r ≤ 250) : r ≠ j := by rcases hj with h|h <;> omega
  refine ⟨⟨?_,?_,h.preserved.tables,?_,h.preserved.available⟩,?_,?_,?_,?_,?_,?_⟩
  · intro r hr; rw [reg r (far r (by rcases hr with h|h|h <;> omega))];exact h.preserved.control r hr
  · rw [reg 8 (far _ (by decide))];exact h.preserved.cursor
  · rw [reg 82 (far _ (by decide))];exact h.preserved.count
  · rw [reg 241 (far _ (by decide))];exact h.bitmap
  · rw [reg 242 (far _ (by decide))];exact h.vector
  · rw [reg 243 (far _ (by decide))];exact h.lengthReg
  · rw [reg 247 (far _ (by decide))];exact h.component
  · rw [reg 250 (far _ (by decide))];exact h.scratch
  · rw [reg 8 (far _ (by decide))];exact h.reserved

private lemma cutSubset {vs : List ℕ} {w : ℕ} {c : List ℕ} (hc : c ∈ cuts vs w) :
    c ⊆ vs ∧ c.length ≤ w := by
  induction vs generalizing w c with
  | nil =>
    have h : c=[] := by simpa [cuts] using hc
    subst c; simp
  | cons v vs ih =>
    cases w with
    | zero => have h : c=[] := by simpa [cuts] using hc
              subst c; simp
    | succ w =>
      rw [cuts,List.mem_append] at hc
      rcases hc with hc|hc
      · obtain ⟨hs,hl⟩ := ih hc
        exact ⟨fun _ hp => List.mem_cons_of_mem _ (hs hp),hl⟩
      · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hc
        obtain ⟨hs,hl⟩ := ih ht
        exact ⟨List.cons_subset_cons _ hs,by simpa using Nat.succ_le_succ hl⟩

private lemma orderFlat {α β γ : Type*} (l : List α) (f : α → Option β) (g : β → List γ) :
    l.flatMap (fun q => (f q).toList.flatMap g) = (l.filterMap f).flatMap g := by
  induction l with
  | nil => rfl
  | cons q qs ih => cases h : f q <;> simp [h,ih]

private lemma dispatch (d : Instance) (w level V M : ℕ) (m : ℤ → ℤ) (z a : State) (cut : List ℕ)
    (seed : ℕ) (az : Between z a) (hc : cut ∈ cuts (vertices d) (min w d.n))
    (inp : CutInput d.n level cut a) (hs : seed ∈ allowed d cut) (ix : a.reg 246=(seed:ℤ))
    (one : a.reg 6=1) (zero : a.reg 7=0) (pos : 0 ≤ a.reg 8) (sz : a.reg 64=(d.n:ℤ))
    (base : a.reg 70=(M:ℤ)) (block : OrdinalSteps d w level m z V)
    (c : List ℕ) (eqc : c=pieceAt d (allowed d cut) seed)
    (head : c.head?=some seed) (row : ComponentArg d.n c a) (len : c.length=level+1) (rim : rimOf d c=cut)
    (ord : (List.range (M^cut.length)).filterMap (ordinalAssignment a cut) = assignments d cut) :
    ∃ t k, Executes d.n m entryProgram a t k ∧
      k ≤ 100+64*(1+d.n)+cut.length*(30+6*M)+(M^cut.length)*(V+5) ∧ Between a t ∧
      t.output=a.output++(assignments d cut).flatMap (entry Naming.name d c) := by
  let s := (a.assign 1076 1).assign 249 1
  obtain ⟨u,j,pu,jt,U⟩ := runPower (n:=d.n) (m:=m) a M cut.length one base inp.lengthReg
  let b := (a.reg 8).toNat
  let u₁ := ((u.clear b d.n).assign 1082 (b:ℤ)).assign 8 ((b+d.n:ℕ):ℤ)
  let u₂ := u₁.assign 250 (u₁.reg 1082)
  have rone := (U.regs 6 (by decide)).trans one
  have rzero := (U.regs 7 (by decide)).trans zero
  have rsize := (U.regs 64 (by decide)).trans sz
  have rcur := U.regs 8 (by decide)
  have bp : (b:ℤ)=a.reg 8 := Int.toNat_of_nonneg pos
  have al : (Operation.alloc 1082 64).next d.n m u = some (u₁,64*(1+d.n)) := by
    simp [Operation.next,u₁,b,rone,rzero,rsize,rcur,pos]
  have fr : OrdinalFrame d.n a u₂ := by
    refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
    · intro r hr
      have ex : r ∉ [1076,249,245,1078,1079] := by simp; rcases hr with h|h|h <;> omega
      have r8 : r≠8 := by rcases hr with h|h|h <;> omega
      have r250 : r≠250 := by rcases hr with h|h|h <;> omega
      have r1082 : r≠1082 := by rcases hr with h|h|h <;> omega
      simpa [u₂,u₁,State.assign,State.clear,r8,r250,r1082] using U.regs r ex
    · simp [u₂,u₁,State.assign,bp]
    · intro i hi
      have off : ¬ (b ≤ i) := by dsimp [b];omega
      simp [u₂,u₁,State.assign,State.clear,off,U.heap]
    · simpa [u₂,u₁,State.assign,State.clear,U.output,U.regs 82 (by decide)] using az.count
    · simpa [u₂,u₁,State.assign,State.clear,U.closed] using az.available
    · simpa [u₂,u₁,State.assign,State.clear] using U.regs 241 (by decide)
    · simpa [u₂,u₁,State.assign,State.clear] using U.regs 242 (by decide)
    · simpa [u₂,u₁,State.assign,State.clear] using U.regs 243 (by decide)
    · simpa [u₂,u₁,State.assign,State.clear] using U.regs 247 (by decide)
    · simp [u₂,u₁,State.assign,State.clear,bp]
    · simp [u₂,u₁,State.assign,State.clear,bp]
  let g := fun q => (ordinalAssignment a cut q).toList.flatMap (entry Naming.name d c)
  let P := fun i (t : State) => OrdinalFrame d.n a t ∧ t.output=a.output++(List.range i).flatMap g
  have starts : P 0 (forSetup 251 1085 249 u₂) :=
    ⟨frameIndex (frameIndex (frameIndex fr (.inl rfl)) (.inr rfl)) (.inr rfl), by simpa [P,forSetup,u₂,u₁,State.assign,State.clear] using U.output⟩
  have total : u₂.reg 249 = ((M^cut.length:ℕ):ℤ) := by simpa [u₂,u₁,State.assign,State.clear] using U.accum
  have Mnat : (a.reg 70).toNat=M := by simp [base]
  obtain ⟨t,k,body,kt,res⟩ := source_for 251 1085 249 (M^cut.length) V ordinalBody P (by decide) (by decide) u₂ total starts (by
    intro q hq t H rq rl
    obtain ⟨y,k,ex,kt,f,yq,yl,oy⟩ := block a cut seed az hc inp hs ix (eqc ▸ head) (eqc ▸ row) (eqc ▸ len) (eqc ▸ rim) q (by simpa [Mnat] using hq) t H.1 rq
    refine ⟨y,k,ex,kt,yq,yl,frameIndex f (.inl rfl),?_⟩
    change y.output=_
    rw [oy,H.2,List.range_succ,List.flatMap_append]
    simp [g,eqc,List.append_assoc])
  rw [entryCode]
  refine ⟨t,_,Executes.seq (.op (o:=.regular (.set 1076 1)) rfl)
    (.seq (.op (o:=.regular (.copy 249 1076)) rfl) (.seq pu (.seq (.op al) (.seq (.op (o:=.regular (.copy 250 1082)) rfl) (.seq body (.skip _)))))),?_,res.1.preserved,?_⟩
  · omega
  · rw [res.2,← ord,← orderFlat]

private lemma envelopeBound (n cap c D b L : ℕ) (e : ℚ) (hn : 2 ≤ n) (hc : n+1 ≤ cap)
    (hL : L ≤ min (widthBound (e:ℝ)) n) (he : 0<e) (he' : e<1) :
    let M := sizes n (budget (e:ℝ))
    let E := parameterEnvelope (e:ℝ)
    100+64*(1+n)+L*(30+6*M)+M^L*(c*cap^D*n^(b*E)+5)
      ≤ (205+c)*cap^(D+1)*n^((b+15)*E) := by
  let O := ownerBound (e:ℝ)
  let E := parameterEnvelope (e:ℝ)
  let W := widthBound (e:ℝ)
  let H := budget (e:ℝ)+1
  let M := sizes n (budget (e:ℝ))
  let F := n^(15*E)
  let P := cap^D*n^(b*E)
  have er : (0:ℝ)<e := by exact_mod_cast he
  have er' : (e:ℝ)<1 := by exact_mod_cast he'
  have op : 1 ≤ O := by
    unfold O ownerBound; apply Nat.le_floor; rw [le_div_iff₀ er]; norm_num; linarith
  have hH : H ≤ 5*O := by dsimp [H,budget,O] at *; omega
  have OW : O*(W+1) ≤ E := by dsimp [O,W,E,parameterEnvelope]; omega
  have leW : L ≤ W := hL.trans (min_le_left _ _)
  have leN : L ≤ n := hL.trans (min_le_right _ _)
  have O1 : O ≤ E := (by simpa using Nat.mul_le_mul_left O (show 1≤W+1 by omega) : O ≤ O*(W+1)).trans OW
  have OL : O*L ≤ E := (Nat.mul_le_mul_left O (by omega : L ≤ W+1)).trans OW
  have Hn : H ≤ n^H := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left hn _)
  have M0 : M ≤ n^(3*H) := by
    change H*n^(2*H) ≤ _
    calc H*n^(2*H) ≤ n^H*n^(2*H) := Nat.mul_le_mul_right _ Hn
         _ = _ := by rw [← pow_add]; congr 1; omega
  have MF : M ≤ F := M0.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have count : M^L ≤ F := by
    calc M^L ≤ (n^(3*H))^L := Nat.pow_le_pow_left M0 L
         _ = n^((3*H)*L) := (pow_mul ..).symm
         _ ≤ F := by
           apply Nat.pow_le_pow_right (by omega)
           calc 3*H*L ≤ 3*(5*O)*L := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hH)
                _ = 15*(O*L) := by ring
                _ ≤ _ := Nat.mul_le_mul_left _ OL
  have p1 : 1 ≤ P := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  have f1 : 1 ≤ F := Nat.pow_pos (by omega)
  have c1 : 1 ≤ cap := by omega
  have pf : 1 ≤ P*F := Nat.mul_pos p1 f1
  have capPF : cap ≤ cap*(P*F) := by simpa using Nat.mul_le_mul_left cap pf
  have boundL : L*(30+6*M) ≤ 36*(cap*(P*F)) := by
    calc L*(30+6*M) ≤ cap*(36*F) := Nat.mul_le_mul (by omega) (by omega)
         _ ≤ cap*(36*(P*F)) := by
           apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left
           simpa using Nat.mul_le_mul_right F p1
         _ = _ := by ring
  have boundQ : M^L*(c*P+5) ≤ (c+5)*(cap*(P*F)) := by
    calc M^L*(c*P+5) ≤ F*((c+5)*P) := Nat.mul_le_mul count (by rw [Nat.add_mul];omega)
         _ = (c+5)*(P*F) := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ (by simpa using Nat.mul_le_mul_right (P*F) c1)
  change 100+64*(1+n)+L*(30+6*M)+M^L*(c*cap^D*n^(b*E)+5) ≤ _
  rw [Nat.mul_assoc c]
  change 100+64*(1+n)+L*(30+6*M)+M^L*(c*P+5) ≤ _
  calc _ ≤ 100*(cap*(P*F))+64*(cap*(P*F))+36*(cap*(P*F))+(c+5)*(cap*(P*F)) := by omega
       _ = _ := by dsimp [P,F]; rw [show (b+15)*E=b*E+15*E by ring,pow_add n,pow_succ cap]; ring

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal

open Scene.CutTraversal Scene.SeparatorLevels TightLanguage
theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    ∀z:Logical.State, Scene.RegionalMenus s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) v z →
    ∀level<x.n, let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
      Scene.CutTraversal.Entries d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ))) := by
  obtain ⟨c,D,b,H⟩ := Root.write_one_boundary_ordinal
  refine ⟨205+c,D+1,b+15,?_⟩
  intro e he he' x s hk hkn ready bounded r p pr pp rr key u prep v geo z menus level hl
  let d := integerData x.n x.mem s.imem r (budget (e:ℝ))
  let w := widthBound (e:ℝ)
  let M := sizes x.n (budget (e:ℝ))
  let E := parameterEnvelope (e:ℝ)
  have block := H e he he' x s hk hkn ready bounded r p pr pp rr key u prep v geo z menus level hl
  change Entries d w level s.imem z ((205+c)*x.cap^(D+1)*x.n^((b+15)*E))
  intro a cut seed az hc inp hs ix
  dsimp only
  intro head row len rim
  obtain ⟨sub,width⟩ := cutSubset hc
  have small (j : ℕ) (hj : j ∈ cut) : j < x.n :=
    List.mem_range.mp (List.mem_filter.mp (sub hj)).1
  have ctl (j : ℕ) (hj : j=6 ∨ j=7 ∨ (64≤j ∧ j≤81)) : a.reg j = u.reg j :=
    (az.control j hj).trans ((menus.controls j (by rcases hj with h|h|h <;> omega)).trans
      (geo.controls j (by rcases hj with h|h|h <;> omega)))
  have prepCopy := prep
  obtain ⟨u1,u0,un,_,_,_,_,_,uM,rest⟩ := prepCopy
  have base : a.reg 70=(M:ℤ) := (ctl 70 (by decide)).trans uM
  have positive : 0 ≤ a.reg 8 := by have h := menus.cursor; have ha:=az.cursor; omega
  have order := boundary_assignments_in_ordinal_order x s r _ _ u v z a (by omega) prep geo menus az cut small
  have o : (List.range (M^cut.length)).filterMap (ordinalAssignment a cut) = assignments d cut := by
    simpa only [ordinalAssignment,base,Int.toNat_natCast,d] using order
  obtain ⟨t,k,run,time,frame,out⟩ := dispatch d w level (c*x.cap^D*x.n^(b*E)) M s.imem z a cut seed az hc inp hs ix
    ((ctl 6 (by decide)).trans u1) ((ctl 7 (by decide)).trans u0) positive ((ctl 64 (by decide)).trans un)
    base block _ rfl head row len rim o
  exact ⟨t,k,run,time.trans (envelopeBound x.n x.cap c D b cut.length e (by omega)
      (by dsimp [World.cap]; omega) width he he'),frame,out⟩
