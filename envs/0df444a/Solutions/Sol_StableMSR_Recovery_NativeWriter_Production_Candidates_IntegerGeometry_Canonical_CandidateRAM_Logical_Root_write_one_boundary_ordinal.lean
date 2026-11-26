-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.write_one_boundary_ordinal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T00:58:48.706392+00:00
-- url     : https://prove2.me/submissions/9bf7bf9e-97e0-4a8d-80a2-419935dfa22a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_decode_boundary_scratch_vector
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_emit_feasible_trials_and_seal
import Definitions.Def_StableMSR_FeasibleEntryEmission
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

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open StableMSR.Recovery.SingleCircuit TightLanguage SeparatorLevels
set_option maxHeartbeats 7000000
private def decoded (M : ℕ) (word : ℕ→ℕ) (check : ℕ→ℕ→Bool) (vs : List ℕ) : ℕ → Option Assignment :=
  vs.foldr (fun v (k : ℕ → Option Assignment) q =>
    if check v (q%M) then (k (q/M)).map (fun t => t++[(v,word (q%M))]) else none) (fun _ => some [])

private lemma accepted_digits (M : ℕ) (word : ℕ→ℕ) (ok : ℕ→ℕ→Bool) (vs : List ℕ) (q : ℕ) :
    (decoded M word ok vs q).isSome =
      (List.range vs.length).all (fun i => ok (vs[i]?.getD 0) (q/M^i%M)) := by
  induction vs generalizing q with
  | nil => simp [decoded]
  | cons v vs ih =>
    change (if ok v (q%M) then (decoded M word ok vs (q/M)).map (fun t => t++[(v,word (q%M))]) else none).isSome = _
    rw [List.length_cons,List.range_succ_eq_map]
    cases h : ok v (q%M) <;> simp [h,List.all_map,Function.comp_def,ih,Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm M]

private lemma scratchValues (h : ℕ→ℤ) (buf L : ℕ) (v f : ℕ→ℕ)
    (inj : ∀ i<L, ∀ j<L, v i = v j → i=j) :
    ∀ i<L, (List.range L).foldl (fun (m : ℕ→ℤ) j => Function.update m (buf+v j) (f j:ℤ)) h (buf+v i) = (f i:ℤ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    intro i hi
    rw [List.range_succ,List.foldl_append]
    by_cases eq : i=L
    · subst i; simp
    · have ii : i<L := by omega
      have ne : buf+v i ≠ buf+v L := by
        intro e; exact eq (inj i hi L (by omega) (by omega))
      simpa [Function.update_of_ne ne] using ih (fun i ai j aj => inj i (by omega) j (by omega)) i ii

private lemma cutFacts (d : Instance) (c cut : List ℕ) (rim : rimOf d c = cut) :
    cut.length ≤ d.n ∧ (∀i<cut.length, reverseVertex cut i < d.n) ∧
      ∀i<cut.length,∀j<cut.length,reverseVertex cut i=reverseVertex cut j → i=j := by
  have nc : cut.Nodup := by rw [← rim]; exact ((List.nodup_range).filter _).filter _
  have sub (p : ℕ) (hp : p∈cut) : p<d.n := by
    rw [← rim] at hp; exact List.mem_range.mp (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  refine ⟨?_,?_,?_⟩
  · rw [← rim]; exact (List.length_filter_le ..).trans ((List.length_filter_le ..).trans (by simp))
  · intro i hi
    have h : i<cut.reverse.length := by simpa using hi
    apply sub
    simpa [reverseVertex,List.getElem?_eq_getElem h] using
      (List.mem_reverse.mp (List.getElem_mem h))
  · intro i hi j hj eq
    have hi' : i<cut.reverse.length := by simpa using hi
    have hj' : j<cut.reverse.length := by simpa using hj
    have eq' : cut.reverse[i] = cut.reverse[j] := by
      simpa [reverseVertex,List.getElem?_eq_getElem hi',List.getElem?_eq_getElem hj'] using eq
    exact (List.Nodup.getElem_inj_iff (List.nodup_reverse.mpr nc)).mp eq'

private def sweepProgram : Program := ((listOf ordinalBody)[3]?).getD .skip
private lemma singleCode : ordinalBody=chain [
    .op (.regular (.copy 252 251)),.op (.regular (.set 1087 1)),.op (.regular (.copy 253 1087)),
    sweepProgram,.cond 6 253 emitFeasible .skip] := rfl

private lemma one_from_emitter (d : Instance) (w level V M : ℕ) (m : ℤ→ℤ) (z a : State) (cut : List ℕ)
    (seed : ℕ) (az : Between z a) (hc : cut ∈ cuts (vertices d) (min w d.n))
    (inp : CutInput d.n level cut a) (hs : seed ∈ allowed d cut) (ix : a.reg 246=(seed:ℤ))
    (one : a.reg 6=1) (positive : 0 ≤ a.reg 8) (base : a.reg 70=(M:ℤ)) (mp : 0<M)
    (bits : ℕ) (ptr : a.reg 81=(bits:ℤ)) (tableEnd : bits+d.n*M ≤ (a.reg 8).toNat)
    (block : FeasibleEmissions d w level m z V)
    (c : List ℕ) (eqc : c=pieceAt d (allowed d cut) seed) (head : c.head?=some seed)
    (row : ComponentArg d.n c a) (len : c.length=level+1) (rim : rimOf d c=cut)
    (q : ℕ) (hq : q<M^cut.length) (t : State) (ft : OrdinalFrame d.n a t) (tq : t.reg 251=(q:ℤ)) :
    ∃ y k, Executes d.n m ordinalBody t y k ∧ k ≤ 30+cut.length*(405+6*M+16*q)+V ∧ OrdinalFrame d.n a y ∧
    y.reg 251=t.reg 251 ∧ y.reg 1085=t.reg 1085 ∧
    y.output = t.output++(ordinalAssignment a cut q).toList.flatMap (entry Naming.name d c) := by
  let s := ((t.assign 252 (t.reg 251)).assign 1087 1).assign 253 1
  let buf := (a.reg 8).toNat
  let dig := fun i => q / M^i % M
  let vs := reverseVertex cut
  obtain ⟨leN,vertices',inject⟩ := cutFacts d c cut rim
  obtain ⟨b,vec,_,vreg,_,vend,_,vread⟩ := inp.rows
  have same (r : ℕ) (hr : r∈[6,70,81,242,243,250]) : s.reg r=t.reg r := by
    simp at hr;rcases hr with h|h|h|h|h|h <;> subst r <;> simp [s,State.assign]
  have memOld (j : ℕ) (hj : j<buf) : s.heap j=a.heap j := ft.preserved.tables j hj
  have hM := (same 70 (by decide)).trans ((ft.preserved.control 70 (by decide)).trans base)
  have h1 := (same 6 (by decide)).trans ((ft.preserved.control 6 (by decide)).trans one)
  have readV (i : ℕ) (hi : i<cut.length) : s.heap (vec+(cut.length-1-i))=(vs i:ℤ) := by
    have off : cut.length-1-i<cut.length := by omega
    rw [memOld _ (by dsimp [buf] at *; omega),vread _ off]
    simp [vs,reverseVertex,List.getElem?_reverse hi,List.getElem?_eq_getElem off]
  have below (i : ℕ) (hi : i<cut.length) : bits+(vs i*M+dig i)<buf := by
    have hv := vertices' i hi
    have hd : dig i<M := Nat.mod_lt _ mp
    have lt : vs i*M+dig i < d.n*M := by
      calc vs i*M+dig i < vs i*M+M := by omega
           _ = (vs i+1)*M := (Nat.succ_mul ..).symm
           _ ≤ _ := Nat.mul_le_mul_right _ hv
    dsimp [buf];omega
  obtain ⟨u,k,ex,tm,_,heap,flag,output,closed,keep⟩ := decode_boundary_scratch_vector d.n m s M q cut.length vec buf bits vs mp
    h1 hM (by simp [s,State.assign,tq]) ((same 243 (by decide)).trans (ft.lengthReg.trans inp.lengthReg))
    ((same 242 (by decide)).trans (ft.vector.trans vreg))
    ((same 250 (by decide)).trans (ft.scratch.trans (Int.toNat_of_nonneg positive).symm))
    ((same 81 (by decide)).trans ((ft.preserved.control 81 (by decide)).trans ptr))
    readV vertices' (by dsimp [buf];omega) tableEnd
  have reg (r : ℕ) (hr : r=6 ∨ r=7 ∨ r=8 ∨ (64≤r ∧ r≤82) ∨ r∈[241,242,243,247,250,251,1085]) :
      u.reg r=t.reg r := by
    have aux : r ∉ [245,1089,1095,1093,1092,1090,254,1097,255,1100,252,1111,1110,1108,1107,1115,253] ∧
      r≠252 ∧ r≠1087 ∧ r≠253 := by simp at hr ⊢;omega
    simpa [s,State.assign,aux] using keep r aux.1
  have uf : OrdinalFrame d.n a u := by
    refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_⟩
    · intro j hj;exact (reg j (by rcases hj with h|h|h <;> omega)).trans (ft.preserved.control j hj)
    · rw [reg 8 (by decide)];exact ft.preserved.cursor
    · intro i hi
      have old (j : ℕ) : (List.range j).foldl (fun (g : ℕ→ℤ) l => Function.update g (buf+vs l) (dig l:ℤ)) s.heap i = s.heap i := by
        induction j with
        | zero => rfl
        | succ j ih =>
          have ne : i ≠ buf+vs j := by change i<buf at hi;omega
          simpa [List.range_succ,List.foldl_append,ne] using ih
      exact (congrFun heap _).trans ((old _).trans (memOld i hi))
    · rw [reg 82 (by decide),output];exact ft.preserved.count
    · rw [closed];exact ft.preserved.available
    · exact (reg 241 (by decide)).trans ft.bitmap
    · exact (reg 242 (by decide)).trans ft.vector
    · exact (reg 243 (by decide)).trans ft.lengthReg
    · exact (reg 247 (by decide)).trans ft.component
    · exact (reg 250 (by decide)).trans ft.scratch
    · rw [reg 8 (by decide)];exact ft.reserved
  have slots (i : ℕ) (hi : i<cut.length) : u.heap (buf+vs i) = (dig i:ℤ) :=
    (congrFun heap _).trans (scratchValues s.heap buf _ vs dig inject i hi)
  have checked := accepted_digits M (fun j => (a.heap ((a.reg 76).toNat+j)).toNat)
    (fun v j => decide (1 ≤ a.heap (bits+(v*M+j)))) cut.reverse q
  have flagEq : u.reg 253=(if (ordinalAssignment a cut q).isSome then 1 else 0) := by
    have vg : (List.range cut.length).all (fun i => decide (1 ≤ s.heap (bits+(vs i*M+dig i)))) =
      (List.range cut.length).all (fun i => decide (1 ≤ a.heap (bits+(vs i*M+dig i)))) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true,List.mem_range,decide_eq_true_eq]
      constructor <;> intro hh i hi
      · simpa only [memOld _ (below i hi)] using hh i hi
      · rw [memOld _ (below i hi)];exact hh i hi
    have test : (ordinalAssignment a cut q).isSome =
        (List.range cut.length).all (fun i => decide (1 ≤ a.heap (bits+(vs i*M+dig i)))) := by
      simpa [ordinalAssignment,decoded,base,ptr,dig,vs,reverseVertex] using checked
    rw [test,← vg];simpa [s,State.assign,dig] using flag
  have uone := (reg 6 (by decide)).trans ((ft.preserved.control 6 (by decide)).trans one)
  have postOut : u.output=t.output := output
  have branch : ∃y j, Executes d.n m (.cond 6 253 emitFeasible .skip) u y j ∧ j≤2+V ∧
      OrdinalFrame d.n a y ∧ y.reg 251=t.reg 251 ∧ y.reg 1085=t.reg 1085 ∧
      y.output=t.output++(ordinalAssignment a cut q).toList.flatMap (entry Naming.name d c) := by
    cases dec : ordinalAssignment a cut q with
    | none =>
      exact ⟨u,2,.no (a:=1) (by simp [flagEq,dec,uone]) (.skip _),by omega,uf,reg 251 (by decide),
        reg 1085 (by decide),by simpa using postOut⟩
    | some ass =>
      obtain ⟨y,j,ej,jt,ff,ix',last',out'⟩ := block a cut seed az hc inp hs ix (eqc ▸ head) (eqc ▸ row)
        (eqc ▸ len) (eqc ▸ rim) q (by simpa [base] using hq) ass dec u uf ((reg 251 (by decide)).trans tq)
        (by simpa [base,buf,vs,dig] using slots)
      exact ⟨y,_,.yes (by simp [flagEq,dec,uone]) ej,by omega,ff,ix'.trans (reg 251 (by decide)),
        last'.trans (reg 1085 (by decide)),by simpa [eqc,postOut] using out'⟩
  obtain ⟨y,j,eb,jt,ff,iy,ly,oy⟩ := branch
  rw [singleCode]
  refine ⟨y,_, .seq (.op (o:=.regular (.copy 252 251)) rfl) (.seq (.op (o:=.regular (.set 1087 1)) rfl)
    (.seq (.op (o:=.regular (.copy 253 1087)) rfl) (.seq ex (.seq eb (.skip _))))),by omega,ff,iy,ly,oy⟩

private lemma singleCost (n cap c D b L q : ℕ) (e : ℚ) (hn : 2 ≤ n) (hc : n+1 ≤ cap)
    (hL : L ≤ min (widthBound (e:ℝ)) n) (he : 0<e) (he' : e<1) (hq : q < (sizes n (budget (e:ℝ)))^L) :
    let M := sizes n (budget (e:ℝ))
    let E := parameterEnvelope (e:ℝ)
    30+L*(405+6*M+16*q)+c*cap^D*n^(b*E)
      ≤ (457+c)*cap^(D+1)*n^((b+15)*E) := by
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

  have qf : q ≤ F := (Nat.le_of_lt hq).trans count
  have fe : F ≤ P*F := by simpa using Nat.mul_le_mul_right F p1
  have pu : P ≤ cap*(P*F) := by
    calc P ≤ P*F := by simpa using Nat.mul_le_mul_left P f1
         _ ≤ cap*(P*F) := by simpa using Nat.mul_le_mul_right (P*F) c1
  have lcost : L*(405+6*M+16*q) ≤ 427*(cap*(P*F)) := by
    calc L*(405+6*M+16*q) ≤ cap*(427*(P*F)) := Nat.mul_le_mul (by omega) (by omega)
         _ = _ := by ring
  have vc := Nat.mul_le_mul_left c pu
  change 30+L*(405+6*M+16*q)+c*cap^D*n^(b*E) ≤ _
  rw [Nat.mul_assoc c]
  change 30+L*(405+6*M+16*q)+c*P ≤ _
  calc _ ≤ 30*(cap*(P*F))+427*(cap*(P*F))+c*(cap*(P*F)) := by omega
       _ = _ := by dsimp [P,F];rw [show (b+15)*E=b*E+15*E by ring,pow_add n,pow_succ cap];ring

private lemma singleCutSubset {vs : List ℕ} {w : ℕ} {c : List ℕ} (hc : c ∈ cuts vs w) :
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


private lemma widthOfCut {vs : List ℕ} {w : ℕ} {c : List ℕ} (hc : c ∈ cuts vs w) : c.length ≤ w :=
  (singleCutSubset hc).2

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
      Scene.CutTraversal.OrdinalSteps d (widthBound (e:ℝ)) level s.imem z (c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ))) := by
  obtain ⟨c,D,b,H⟩ := Root.emit_feasible_trials_and_seal
  refine ⟨457+c,D+1,b+15,?_⟩
  intro e he he' x s hk hkn ready bound r p pr pp rr key u prep v geo z menus level hl
  let h := budget (e:ℝ)
  let w := widthBound (e:ℝ)
  let E := parameterEnvelope (e:ℝ)
  let d := integerData x.n x.mem s.imem r h
  let M := sizes x.n h
  let o := offsets x.n M
  let bit := cursorAt o 10
  have block := H e he he' x s hk hkn ready bound r p pr pp rr key u prep v geo z menus level hl
  change OrdinalSteps d w level s.imem z ((457+c)*x.cap^(D+1)*x.n^((b+15)*E))
  intro a cut seed az hc inp hs ix
  dsimp only
  intro head row len rim q hq t ft tq
  have ctl (j : ℕ) (hj : j=6 ∨ j=7 ∨ (64≤j ∧ j≤81)) : a.reg j = u.reg j :=
    (az.control j hj).trans ((menus.controls j (by rcases hj with h|h|h <;> omega)).trans
      (geo.controls j (by rcases hj with h|h|h <;> omega)))
  obtain ⟨u1,_,_,_,_,_,_,_,uM,_,_,ptrs,_⟩ := prep
  have base : a.reg 70=(M:ℤ) := (ctl 70 (by decide)).trans uM
  have bitsPtr : a.reg 81=(bit:ℤ) := (ctl 81 (by decide)).trans (ptrs ⟨10,by decide⟩)
  have endB : bit+x.n*M ≤ cursorAt o 11 := by simp [bit,o,cursorAt,offsets];omega
  have high := menus.cursor
  change (cursorAt o 11:ℤ) ≤ z.reg 8 at high
  have cur := az.cursor
  have nx : 0 < x.n := by omega
  have mp : 0<M := by dsimp [M,sizes]; positivity
  have qSmall : q < M^cut.length := by simpa [base] using hq
  obtain ⟨y,k,ex,time,fr,iy,ly,oy⟩ := one_from_emitter d w level (c*x.cap^D*x.n^(b*E)) M s.imem z a cut seed az hc inp hs ix
    ((ctl 6 (by decide)).trans u1) (by omega) base mp bit bitsPtr (by change bit+x.n*M ≤ _;omega) block _ rfl head row len rim q qSmall t ft tq
  exact ⟨y,k,ex,time.trans (singleCost x.n x.cap c D b cut.length q e (by omega)
      (by dsimp [World.cap];omega) (widthOfCut hc) he he' qSmall),fr,iy,ly,oy⟩
