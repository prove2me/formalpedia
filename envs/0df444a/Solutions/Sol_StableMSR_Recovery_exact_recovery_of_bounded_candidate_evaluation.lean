-- Prove2me | solution 1 for StableMSR.Recovery.exact_recovery_of_bounded_candidate_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:40:45.547807+00:00
-- url     : https://prove2.me/submissions/f8f50c56-01bc-4f77-ace6-f8a0e3f2c4f4

import Definitions.Def_StableMSR_BallCoverCatalog
import Definitions.Def_StableMSR_CandidateInterpreter
import Definitions.Def_StableMSR_CanonicalRegionalCompiler
import Definitions.Def_StableMSR_DenseSingletonCompilation
import Definitions.Def_StableMSR_FewBallRows
import Definitions.Def_StableMSR_LocalBallTrials
import Definitions.Def_StableMSR_Recovery_Execution
import Definitions.Def_StableMSR_RegionalBallDP
import Definitions.Def_StableMSR_SingleWindowGrammar
import Definitions.Def_StableMSR_WindowBlockMasks
import Definitions.Def_StableMSR_WindowCSP
import Definitions.Def_StableMSR_WindowJoins
import Definitions.Def_StableMSR_WindowPorts
import Definitions.Def_StableMSR_WindowProfiles
import Theorems.Thm_StableMSR_Recovery_BallCoverCatalog_cheapest_cover_recovers
import Theorems.Thm_StableMSR_Recovery_BallCoverCatalog_selector_expression
import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_cartesian_row_machine
import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_cartesian_rows_certify_partitions
import Theorems.Thm_StableMSR_Recovery_CartesianBallRows_singleton_cover_machine
import Theorems.Thm_StableMSR_Recovery_Compiler_compiler_execution_exact
import Theorems.Thm_StableMSR_Recovery_FewBallRows_append_few_large_recovery
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_bounded_run_is_native
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_assembly_recognizes_original
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_computed_integer_instance
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_integer_instance_exact
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_native_metric_table
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_native_candidate_filter
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_unfiltered_scan_is_exact
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_native_chart_packet_decoder
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_native_slot_classification
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_ordered_production_replay
import Theorems.Thm_StableMSR_Recovery_OracleQueries_point_output_loop
import Theorems.Thm_StableMSR_Recovery_RegionalBallDP_decode_regional_menus
import Theorems.Thm_StableMSR_Recovery_RegionalBallDP_disjoint_local_menus_certify_terminal
import Theorems.Thm_StableMSR_Recovery_SingleRAM_native_board_realizes_circuit_language
import Theorems.Thm_StableMSR_Recovery_SingleRAM_native_circuit_record_emitter
import Theorems.Thm_StableMSR_Recovery_SingleWindows_singleton_board_describes_regional_incidences
import Theorems.Thm_StableMSR_Recovery_WindowCSP_aligned_scenario_has_exact_assignment
import Theorems.Thm_StableMSR_Recovery_WindowCSP_catalog_to_local_trials
import Theorems.Thm_StableMSR_Recovery_WindowCSP_dense_aligned_scenario_program
import Theorems.Thm_StableMSR_Recovery_WindowJoins_native_join_decoder
import Theorems.Thm_StableMSR_Recovery_WindowMasks_native_block_literal_compiler
import Theorems.Thm_StableMSR_Recovery_WindowPorts_native_count_expansion
import Theorems.Thm_StableMSR_Recovery_WindowProfiles_local_profiles_certify_exact_count_search
import Theorems.Thm_StableMSR_Recovery_WindowProfiles_native_count_graph
import Theorems.Thm_StableMSR_Recovery_parameterEnvelope_bound
import Theorems.Thm_StableMSR_Recovery_validLabels_feasible
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
section MachineBridge
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Naming
open SingleCircuit
theorem push_pos (a z:ℕ) : 0<push a z := by induction z <;> simp [push] <;> omega
theorem push_inj (a b x y:ℕ) (h:push a x=push b y) : a=b ∧ x=y := by
  induction x generalizing y with
  | zero=>cases y <;> simp only [push] at h <;> omega
  | succ x ih=>
    cases y with
    | zero=>simp only [push] at h;omega
    | succ y=>
      simp only [push] at h
      obtain ⟨eq,eq'⟩:=ih y (by omega);exact ⟨eq,by omega⟩

theorem code_inj : Function.Injective code := by
  intro xs;induction xs with
  | nil=>
    intro ys h;cases ys with
    | nil=>rfl
    | cons y ys=>have :=push_pos (code ys) y;change 0=push (code ys) y at h;omega
  | cons x xs ih=>
    intro ys h;cases ys with
    | nil=>have :=push_pos (code xs) x;change push (code xs) x=0 at h;omega
    | cons y ys=>
      obtain ⟨tail,eq⟩:=push_inj _ _ _ _ h
      rw [eq,ih tail]

theorem pair_inj : Function.Injective pairs := by
  intro xs;induction xs with
  | nil=>intro ys h;cases ys <;> simp_all [pairs]
  | cons p xs ih=>
    intro ys h;cases ys with
    | nil=>simp [pairs] at h
    | cons q ys=>
      change p.1::p.2::pairs xs=q.1::q.2::pairs ys at h
      simp only [List.cons.injEq] at h
      rw [Prod.ext h.1 h.2.1,ih h.2.2]

theorem split_digits (c c' a a':List ℕ)
    (h:c.map Nat.succ++(0::a)=c'.map Nat.succ++(0::a')) : c=c' ∧ a=a' := by
  induction c generalizing c' with
  | nil=>cases c' <;> simp_all
  | cons p c ih=>
    cases c' with
    | nil=>simp at h
    | cons q c'=>
      simp only [List.map_cons,List.cons_append,List.cons.injEq,Nat.succ.injEq] at h
      obtain ⟨he,ha⟩:=ih c' h.2;exact ⟨by rw [h.1,he],ha⟩

theorem name_injective : Function.Injective name := by
  rintro ⟨c,a⟩ ⟨c',a'⟩ h
  have eq:=congrArg List.reverse (code_inj h)
  simp only [List.reverse_reverse,digits,List.append_assoc,List.singleton_append] at eq
  obtain ⟨cEq,aEq⟩:=split_digits _ _ _ _ eq
  exact Prod.ext cEq (pair_inj aEq)

theorem accumulated (xs:List ℕ) : xs.foldl push 0=code xs.reverse := by
  induction xs using List.reverseRecOn with
  | nil=>rfl
  | append_singleton xs a ih=>simp [List.foldl_append,ih,code]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Naming
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open Compiler OracleQueries WindowCSP SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem to_raw (checked : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃F t,F≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    CandidateRAM.run F [CandidateRAM.code (budget (e:ℝ)) (widthBound (e:ℝ))] (CandidateRAM.banks s)=some t ∧
    (∀q:ℤ,(∀i:ℕ,q≠cell 5 i ∧ q≠cell 7 i) → t.mem q=s.imem q) ∧
    Candidates.Input x.n t.mem (tape CandidateRAM.Naming.name (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))))
    (execution : ∀ {n:ℕ} (d:Fin n→Fin n→ℝ) (s:Store) (h w fuel:ℕ) (t:Banks),
      run fuel [code h w] (banks s)=some t →
      ∃z,Executes d (program h w) s (restore s t) z ∧ z≤2*fuel ∧ (∀j<6,t.reg j=s.ptrs j))
    (injective:Function.Injective Naming.name) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,IntegerCmd cmd ∧
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes (fun (_ _:Fin x.n)=>(0:ℝ)) cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      Input x.n t.imem (tape enc (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))) := by
  obtain ⟨c,D,b,ok⟩:=checked
  refine ⟨2*c,D,b,?_⟩
  intro e he hl
  let h:=budget (e:ℝ)
  let w:=widthBound (e:ℝ)
  refine ⟨program h w,integer h w,?_⟩
  intro x s hk kn rd bounded r p regR regP live key
  obtain ⟨F,t,cf,done,frame,tapeOK⟩:=ok e he hl x s hk kn rd bounded r p regR regP live key
  obtain ⟨z,ex,steps,regs⟩:=execution (fun (_ _:Fin x.n)=>(0:ℝ)) s h w F t done
  refine ⟨restore s t,z,ex,?_,?_,?_,?_,Naming.name,injective,tapeOK⟩
  · apply steps.trans
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 cf
  · refine ⟨fun ax=>(regs _ (by cases ax <;> decide)).trans (rd.1 ax),?_⟩
    intro q;exact (frame (q:ℤ) (by intro i;unfold cell word;push_cast;constructor <;> omega)).trans (rd.2 q)
  · intro i hi;exact regs i (by simp at hi;omega)
  · intro j lo hi a
    apply frame
    intro i;unfold cell word;push_cast;constructor <;> omega
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.native_source_of_evaluation (evaluated : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃F t,F≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    CandidateRAM.run F [CandidateRAM.code (budget (e:ℝ)) (widthBound (e:ℝ))] (CandidateRAM.banks s)=some t ∧
    (∀q:ℤ,(∀i:ℕ,q≠cell 5 i ∧ q≠cell 7 i) → t.mem q=s.imem q) ∧
    Candidates.Input x.n t.mem (tape CandidateRAM.Naming.name (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)))) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,IntegerCmd cmd ∧
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes (fun (_ _:Fin x.n)=>(0:ℝ)) cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      Input x.n t.imem (tape enc (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))) :=
  CandidateRAM.to_raw evaluated CandidateRAM.bounded_run_is_native CandidateRAM.Naming.name_injective
end MachineBridge
section WriterBridge
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def imperative {S V:Type} (E:Algebra S V) (d:Instance) (w:ℕ) : S×V := Id.run do
  let all:=vertices d
  let small:=cuts all (min w d.n)
  let mut g:=E.initial
  let mut tab : Table V:=[]
  for k in List.range d.n do
    for s in small do
      for c in keysFor d all s do
        if c.length==k+1 && rimOf d c==s then
          for a in assignments d s do
            let mut acc:=E.fail
            for v in c do
              for x in d.menu v do
                let b:=(v,x)::a
                if localOK d b then
                  if let some ids:=refs d tab c v b then
                    let pair:=E.alternative g acc v x ids
                    g:=pair.1
                    acc:=pair.2
            tab:=((c,a),acc)::tab
  if let some ids:=(parts d all).mapM (m:=Option) (fun c=>lookup tab c []) then return E.finish g ids
  return (g,E.fail)

def body (g : Gates) (masks : List (List ℕ)) (sons : List ℕ) : Gates×ℕ := Id.run do
  let mut a:=g
  let mut tail:=0
  for m in masks do
    let l:=a.size
    a:=a.push (.atom m)
    let p:=a.size
    a:=a.push (.both tail l)
    tail:=p
  for s in sons do
    let p:=a.size
    a:=a.push (.both tail s)
    tail:=p
  return (a,tail)

def gateAlgebra (d:Instance) : Algebra Gates ℕ where
  initial:=#[.atom [],.stop]
  fail:=1
  alternative:=fun g acc v x ids=>
    let pair:=body g (d.owned v x) ids
    (pair.1.push (.either acc pair.2),pair.1.size)
  finish:=fun g ids=>body g [] ids

theorem loop_eq {A B:Type} (l:List A) (b:B) (f:A→B→Id (ForInStep B)) (g:B→A→B)
    (step:∀a b,f a b=.yield (g b a)) : (forIn l b f:Id B)=l.foldl g b := by
  have eq:f=(fun a b=>pure (ForInStep.yield (g b a))):=by funext a b;exact step a b
  rw [eq];exact List.forIn_pure_yield_eq_foldl _ _

end StableMSR.Recovery.TightLanguage

namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

theorem source_eq (d:Instance) (w:ℕ) : compileRegion d w=imperative (gateAlgebra d) d w := by
  set_option smartUnfolding false in rfl

section
variable {S V:Type} (E:Algebra S V) (d:Instance)

def offerLoop (tab:Table V) (c:List ℕ) (a:Assignment) (v x:ℕ) (p:S×V) : ForInStep (S×V) :=
  let b:=(v,x)::a
  if localOK d b then
    match refs d tab c v b with
    | some ids=>.yield (E.alternative p.1 p.2 v x ids)
    | _=>.yield p
  else .yield p

def optionLoop (tab:Table V) (c:List ℕ) (a:Assignment) (g:S) : S×V :=
  Id.run (forIn c (g,E.fail) (fun v p=>pure (.yield
    (Id.run (forIn (d.menu v) p (fun x q=>pure (offerLoop E d tab c a v x q)))))))

theorem options_fold (tab:Table V) (c:List ℕ) (a:Assignment) (g:S) :
    optionLoop E d tab c a g=collect E d tab c a g := by
  unfold optionLoop collect
  apply loop_eq
  intro v p;apply congrArg ForInStep.yield
  apply loop_eq
  intro x q
  by_cases ok:localOK d ((v,x)::a)=true
  · cases result:refs d tab c v ((v,x)::a) <;> simp only [offerLoop,offer,ok,result,if_true] <;> rfl
  · simp only [offerLoop,offer,ok,if_false];rfl

def assignmentLoop (c:List ℕ) (a:Assignment) (p:S×Table V) : S×Table V :=
  let b:=optionLoop E d p.2 c a p.1
  (b.1,((c,a),b.2)::p.2)

def componentLoop (k:ℕ) (s c:List ℕ) (p:S×Table V) : ForInStep (S×Table V) :=
  if c.length==k+1 && rimOf d c==s then
    .yield (Id.run (forIn (assignments d s) p (fun a q=>pure (.yield (assignmentLoop E d c a q)))))
  else .yield p

def tableLoop (w:ℕ) : S×Table V :=
  let vs:=vertices d
  let ss:=cuts vs (min w d.n)
  Id.run (forIn (List.range d.n) (E.initial,([]:Table V)) (fun k p=>pure (.yield
    (Id.run (forIn ss p (fun s q=>pure (.yield
      (Id.run (forIn (keysFor d vs s) q (fun c z=>pure (componentLoop E d k s c z)))))))))))

theorem table_fold (w:ℕ) : tableLoop E d w=build E d w := by
  unfold tableLoop build
  apply loop_eq;intro k p;apply congrArg ForInStep.yield
  apply loop_eq;intro s q;apply congrArg ForInStep.yield
  apply loop_eq;intro c z
  unfold componentLoop visit;split
  · apply congrArg ForInStep.yield
    apply loop_eq;intro a t
    simp only [assignmentLoop,install,options_fold];rfl
  · rfl

def rawTable {S V:Type} (E:Algebra S V) (d:Instance) (w:ℕ) : S×Table V := Id.run do
  let all:=vertices d
  let small:=cuts all (min w d.n)
  let mut g:=E.initial
  let mut tab : Table V:=[]
  for k in List.range d.n do
    for s in small do
      for c in keysFor d all s do
        if c.length==k+1 && rimOf d c==s then
          for a in assignments d s do
            let mut acc:=E.fail
            for v in c do
              for x in d.menu v do
                let b:=(v,x)::a
                if localOK d b then
                  if let some ids:=refs d tab c v b then
                    let pair:=E.alternative g acc v x ids
                    g:=pair.1
                    acc:=pair.2
            tab:=((c,a),acc)::tab
  return (g,tab)

theorem raw_eq (w:ℕ) : rawTable E d w=tableLoop E d w := by
  set_option smartUnfolding false in rfl

theorem normalized (w:ℕ) : imperative E d w=scan E d w := by
  let st:=rawTable E d w
  have raw: imperative E d w=(if let some ids:=(parts d (vertices d)).mapM (m:=Option) (fun c=>lookup st.2 c []) then E.finish st.1 ids else (st.1,E.fail)):=by
    set_option smartUnfolding false in rfl
  rw [raw]
  unfold scan
  have eq:st=build E d w:=(raw_eq E d w).trans (table_fold E d w)
  rw [eq]
  dsimp only
  cases z:(parts d (vertices d)).mapM (m:=Option) (fun c=>lookup (build E d w).2 c []) <;> rfl
end
end StableMSR.Recovery.TightLanguage
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
theorem body_fold (g:Gates) (ms:List (List ℕ)) (ids:List ℕ) :
    body g ms ids=ids.foldl sonStep (ms.foldl litStep (g,0)) := by
  let ml:=fun (m:List ℕ) (z:Gates×ℕ)=>(pure (.yield (litStep z m)):Id (ForInStep (Gates×ℕ)))
  let sl:=fun (p:ℕ) (z:Gates×ℕ)=>(pure (.yield (sonStep z p)):Id (ForInStep (Gates×ℕ)))
  change (forIn ids (forIn ms (g,0) ml:Id (Gates×ℕ)) sl:Id (Gates×ℕ))=_
  rw [loop_eq ms _ ml litStep (fun _ _=>rfl),loop_eq ids _ sl sonStep (fun _ _=>rfl)]

end StableMSR.Recovery.TightLanguage
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false

theorem fold_gain {S I : Type} (size : S → ℕ) (xs : List I) (step : S → I → S) (z : S) (C : ℕ)
    (h : ∀ p i, i ∈ xs → size (step p i) ≤ size p + C) :
    size (xs.foldl step z) ≤ size z + xs.length * C := by
  induction xs generalizing z with
  | nil => simp
  | cons i xs ih =>
    simp only [List.foldl_cons,List.length_cons,Nat.succ_mul]
    have a := h z i (by simp)
    have b := ih (step z i) (fun p j hj => h p j (by simp [hj]))
    omega

theorem flat_length {I O : Type} (xs : List I) (f : I → List O) (B : ℕ)
    (h : ∀ i, i ∈ xs → (f i).length ≤ B) : (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    have a := h i (by simp)
    have b := ih (fun j hj => h j (by simp [hj]))
    omega

theorem body_bound (g : Gates) (ms : List (List ℕ)) (vs : List ℕ) :
    (body g ms vs).1.size ≤ g.size + 2*ms.length + vs.length := by
  rw [body_fold]
  have a := fold_gain (fun z : Gates×ℕ => z.1.size) ms litStep (g,0) 2
    (fun p i _ => by simp [litStep])
  have b := fold_gain (fun z : Gates×ℕ => z.1.size) vs sonStep (ms.foldl litStep (g,0)) 1
    (fun p i _ => by simp [sonStep])
  dsimp only at a b
  omega

theorem some_length {I O : Type} (f : I → Option O) (xs : List I) (ys : List O)
    (h : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simpa [List.mapM_nil] using congrArg (fun q : Option (List O) => (q.getD []).length) h.symm
  | cons i xs ih =>
    rw [List.mapM_cons] at h
    cases a : f i with
    | none => simp [a] at h
    | some v =>
      cases b : xs.mapM f with
      | none => simp [a,b] at h
      | some vs =>
        simp [a,b] at h
        subst ys
        simp [ih _ b]

theorem assignments_bound (d : Instance) (K : ℕ) (hK : ∀ v, (d.menu v).length ≤ K) (s : List ℕ) :
    (assignments d s).length ≤ K^s.length := by
  induction s with
  | nil => simp [assignments]
  | cons v s ih =>
    unfold assignments
    apply Nat.le_trans (flat_length _ _ (K^s.length) (fun x _ => by simpa using ih))
    simpa [Nat.pow_succ,Nat.mul_comm] using Nat.mul_le_mul_right (K^s.length) (hK v)

theorem cut_size (vs : List ℕ) (w : ℕ) (s : List ℕ) (h : s ∈ cuts vs w) : s.length ≤ w := by
  induction vs generalizing w s with
  | nil => simp [cuts] at h; simp [h]
  | cons v vs ih =>
    cases w with
    | zero => simp [cuts] at h; simp [h]
    | succ w =>
      rw [cuts,List.mem_append] at h
      rcases h with h | h
      · exact ih _ _ h
      · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
        simpa using ih _ _ ht

theorem cuts_count (vs : List ℕ) (w : ℕ) : (cuts vs w).length ≤ (vs.length+1)^w := by
  induction vs generalizing w with
  | nil => simp [cuts]
  | cons v vs ih =>
    cases w with
    | zero => simp [cuts]
    | succ w =>
      rw [cuts,List.length_append,List.length_map,List.length_cons]
      calc
        _ ≤ (vs.length+1)^(w+1) + (vs.length+1)^w := Nat.add_le_add (ih _) (ih _)
        _ = (vs.length+1)^w * (vs.length+1+1) := by simp only [Nat.pow_succ,Nat.mul_succ]
        _ ≤ _ := by rw [Nat.pow_succ]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)

theorem parts_count (d : Instance) (allowed : List ℕ) : (parts d allowed).length ≤ allowed.length :=
  List.length_filterMap_le .. 

theorem refs_count (d : Instance) {V : Type} (tab : Table V) (c : List ℕ) (v : ℕ) (a : Assignment)
    (ids : List V) (h : refs d tab c v a = some ids) : ids.length ≤ c.length := by
  rw [some_length _ _ _ h]
  exact Nat.le_trans (parts_count d _) List.length_erase_le

end StableMSR.Recovery.TightLanguage

namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 700000

def gateEnvelope (N M B w : ℕ) := 2+N*((N+1)^w*(N*M^w)*((N*M)*(2*B+N+2)))+N

theorem offer_bound (d : Instance) (B : ℕ) (hB : ∀ v x, (d.owned v x).length ≤ B)
    (tab : Table ℕ) (c : List ℕ) (a : Assignment) (v x : ℕ) (p : Gates × ℕ) :
    (offer (gateAlgebra d) d tab c a v x p).1.size ≤ p.1.size + (2*B+c.length+2) := by
  unfold offer
  dsimp only
  split
  · split
    next ids eq =>
      change (Array.push (body p.1 (d.owned v x) ids).1 _).size ≤ _
      rw [Array.size_push]
      have h := body_bound p.1 (d.owned v x) ids
      have k := refs_count _ _ _ _ _ _ eq
      have b := hB v x
      omega
    next => omega
  · omega

theorem collect_bound (d : Instance) (K B : ℕ) (hK : ∀ v, (d.menu v).length ≤ K)
    (hB : ∀ v x, (d.owned v x).length ≤ B) (tab : Table ℕ) (c : List ℕ) (a : Assignment)
    (g : Gates) (hc : c.length ≤ d.n) :
    (collect (gateAlgebra d) d tab c a g).1.size ≤ g.size + (d.n*K)*(2*B+d.n+2) := by
  let C := 2*B+d.n+2
  unfold collect
  have outer := fold_gain (fun p : Gates×ℕ => p.1.size) c
    (fun p v => (d.menu v).foldl (fun st x => offer (gateAlgebra d) d tab c a v x st) p)
    (g,(gateAlgebra d).fail) (K*C) (by
      intro p v _
      apply Nat.le_trans (fold_gain (fun q : Gates×ℕ => q.1.size) _ _ _ C ?_)
      · exact Nat.add_le_add_left (Nat.mul_le_mul_right C (hK v)) _
      · intro st x _
        have e := offer_bound d B hB tab c a v x st
        dsimp only [C] at *
        omega)
  apply Nat.le_trans outer
  dsimp only
  rw [←Nat.mul_assoc]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right C (Nat.mul_le_mul_right K hc)) _

theorem visit_bound (d : Instance) (K B w : ℕ) (h0 : 0<K) (hK : ∀ v, (d.menu v).length ≤ K)
    (hB : ∀ v x, (d.owned v x).length ≤ B) (k : ℕ) (s c : List ℕ)
    (p : Gates × Table ℕ) (hk : k < d.n) (hs : s.length ≤ w) :
    (visit (gateAlgebra d) d k s c p).1.size ≤ p.1.size + K^w*((d.n*K)*(2*B+d.n+2)) := by
  unfold visit
  split
  next e =>
    have e' : c.length=k+1 := by
      simp only [Bool.and_eq_true,beq_iff_eq] at e
      exact e.1
    have hb := fold_gain (fun t : Gates×Table ℕ => t.1.size) (assignments d s)
      (fun t a => install (gateAlgebra d) d c a t) p ((d.n*K)*(2*B+d.n+2))
      (fun t a _ => collect_bound d K B hK hB t.2 c a t.1 (by omega))
    exact Nat.le_trans hb (Nat.add_le_add_left (Nat.mul_le_mul_right _
      (Nat.le_trans (assignments_bound d K hK s) (Nat.pow_le_pow_right h0 hs))) _)
  next => omega

theorem table_count (d : Instance) (w K B : ℕ) (h0 : 0<K) (hK : ∀ v, (d.menu v).length ≤ K)
    (hB : ∀ v x, (d.owned v x).length ≤ B) :
    (build (gateAlgebra d) d w).1.size ≤ 2+d.n*((d.n+1)^w*(d.n*K^w)*((d.n*K)*(2*B+d.n+2))) := by
  let vs := vertices d
  let seps := cuts vs (min w d.n)
  let C := (d.n*K)*(2*B+d.n+2)
  let V := K^w*C
  have hv : vs.length ≤ d.n := by
    exact Nat.le_trans (List.length_filter_le ..) (by simp)
  have hs : seps.length ≤ (d.n+1)^w := Nat.le_trans (cuts_count vs _) (Nat.le_trans
    (Nat.pow_le_pow_left (by omega : vs.length+1 ≤ d.n+1) _) (Nat.pow_le_pow_right (by omega) (Nat.min_le_left ..)))
  have hkey (s : List ℕ) : (keysFor d vs s).length ≤ d.n := Nat.le_trans
    (parts_count d _) (Nat.le_trans (List.length_filter_le ..) hv)
  have per (p : Gates×Table ℕ) (k : ℕ) (hk : k∈List.range d.n) (s : List ℕ) (hmem : s∈seps) :
      ((keysFor d vs s).foldl (fun t c => visit (gateAlgebra d) d k s c t) p).1.size ≤ p.1.size+d.n*V := by
    apply Nat.le_trans (fold_gain (fun t : Gates×Table ℕ => t.1.size) _ _ _ V
      (fun t c _ => visit_bound d K B w h0 hK hB k s c t (List.mem_range.mp hk)
        (Nat.le_trans (cut_size vs _ s hmem) (Nat.min_le_left ..))))
    exact Nat.add_le_add_left (Nat.mul_le_mul_right V (hkey s)) _
  let step := fun (p : Gates×Table ℕ) (k : ℕ) => seps.foldl (fun z s =>
    (keysFor d vs s).foldl (fun t c => visit (gateAlgebra d) d k s c t) z) p
  have mid (p : Gates×Table ℕ) (k : ℕ) (hk : k∈List.range d.n) :
      (step p k).1.size ≤ p.1.size+(d.n+1)^w*(d.n*V) := by
    apply Nat.le_trans (fold_gain (fun t : Gates×Table ℕ => t.1.size) _ _ _ (d.n*V)
      (fun t s ht => per t k hk s ht))
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hs) _
  have top := fold_gain (fun t : Gates×Table ℕ => t.1.size) (List.range d.n) step
    ((gateAlgebra d).initial,[]) ((d.n+1)^w*(d.n*V)) mid
  change ((List.range d.n).foldl step ((gateAlgebra d).initial,[])).1.size ≤ _
  have base : (gateAlgebra d).initial.size=2 := rfl
  simpa only [base,V,C,List.length_range,Nat.mul_assoc] using top

theorem circuit_count (d : Instance) (w K B : ℕ) (h0 : 0<K) (hK : ∀ v, (d.menu v).length ≤ K)
    (hB : ∀ v x, (d.owned v x).length ≤ B) :
    (compileRegion d w).1.size ≤ gateEnvelope d.n K B w := by
  rw [source_eq,normalized]
  let st := build (gateAlgebra d) d w
  have ht := table_count d w K B h0 hK hB
  change st.1.size ≤ _ at ht
  have hp : (parts d (vertices d)).length ≤ d.n := Nat.le_trans (parts_count d _)
    (Nat.le_trans (List.length_filter_le ..) (by simp))
  unfold scan
  dsimp only
  rw [← show st = build (gateAlgebra d) d w from rfl]
  split
  next ids eq =>
    have he := some_length _ _ _ eq
    have hb := body_bound st.1 [] ids
    change (body st.1 [] ids).1.size ≤ _
    simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at hb
    unfold gateEnvelope
    omega
  next =>
    unfold gateEnvelope
    dsimp only
    omega

end StableMSR.Recovery.TightLanguage

namespace StableMSR.Recovery.TightLanguage
open OracleQueries SingleCircuit SingleCodes
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

def menuLimit (n h : ℕ) := (h+1)*n^(2*(h+1))

theorem integer_gate_count (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ) (hn : 1 ≤ x.n) :
    (regionalCircuit x W R h w).1.size ≤ gateEnvelope x.n (menuLimit x.n h) x.n w := by
  let K := menuLimit x.n h
  have pos : 0<K := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have words : (SingleCodes.words x.n h).length ≤ K := by
    apply (flat_length _ _ (CartesianBallRows.rows x.n (h+1)) ?_).trans
    · simp [K,menuLimit,CartesianBallRows.rows]
    · intro a ha; simp
  apply circuit_count _ _ K x.n pos
  · intro v
    simp only [SingleCodes.instanceOf,SingleCodes.lookup]
    split
    · exact (List.length_filter_le ..).trans words
    · simp
  · intro v a
    simp only [SingleCodes.instanceOf,SingleCodes.lookup]
    split
    · simp only [blockList,List.length_map,Finset.length_toList]
      apply (Finset.card_filter_le ..).trans
      apply Finset.card_image_le.trans
      simpa using (Finset.card_le_univ (WindowCSP.window x.dist W R ⟨v,by assumption⟩))
    · simp


theorem envelope_power (n h w : ℕ) (hn:2≤n) :
    gateEnvelope n (menuLimit n h) n w ≤ n^(15*((h+1)*(w+1))) := by
  let p:=(h+1)*(w+1)
  let A:=n^p
  have h1:1≤h+1:=by omega
  have w1:1≤w+1:=by omega
  have hw:h+1≤p:=Nat.le_mul_of_pos_right _ w1
  have wp:w≤p:=by have e:=Nat.le_mul_of_pos_left (w+1) h1;omega
  have pp:1≤p:=h1.trans hw
  have na:n≤A:=by simpa [A] using (Nat.pow_le_pow_right (show 1≤n by omega) pp)
  have aa:2≤A:=hn.trans na
  have k: menuLimit n h≤n^(3*(h+1)) := by
    have hh:h+1≤n^(h+1):=(Nat.le_of_lt (Nat.lt_two_pow_self (n:=h+1))).trans (Nat.pow_le_pow_left hn _)
    calc _ ≤ n^(h+1)*n^(2*(h+1)) := Nat.mul_le_mul_right _ hh
         _ = _ := by rw [←pow_add];congr 1;omega
  have kw:(menuLimit n h)^w≤A^3 := by
    apply (Nat.pow_le_pow_left k w).trans
    rw [←pow_mul,show A^3=n^(p*3) from (pow_mul ..).symm]
    apply Nat.pow_le_pow_right (by omega)
    dsimp [p];nlinarith
  have k0:menuLimit n h≤A^3:=by
    apply k.trans
    rw [show A^3=n^(p*3) from (pow_mul ..).symm]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have nw:(n+1)^w≤A^2 := by
    have plus:n+1≤n^2:=by nlinarith [Nat.mul_le_mul_right n hn]
    apply (Nat.pow_le_pow_left plus w).trans
    rw [←pow_mul,show A^2=n^(p*2) from (pow_mul ..).symm]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have three:2*n+n+2≤A^3 := by
    have sq:2*A≤A*A:=Nat.mul_le_mul_right A aa
    have cube:2*(A*A)≤A*(A*A):=Nat.mul_le_mul_right _ aa
    nlinarith
  have big:n*((n+1)^w*(n*(menuLimit n h)^w)*((n*menuLimit n h)*(2*n+n+2)))≤A^14 := by
    calc _ ≤ A*(A^2*(A*A^3)*((A*A^3)*A^3)) := Nat.mul_le_mul na (Nat.mul_le_mul
              (Nat.mul_le_mul nw (Nat.mul_le_mul na kw)) (Nat.mul_le_mul (Nat.mul_le_mul na k0) three))
         _ = _ := by ring
  have rest:2+n≤A^14 := by
    apply (show 2+n≤A^2 by nlinarith [Nat.mul_le_mul_right A aa]).trans
    exact Nat.pow_le_pow_right (by omega) (by decide)
  change 2+_+n≤_
  calc _ ≤ A^14+A^14 := by omega
       _ = 2*A^14 := by omega
       _ ≤ A*A^14 := Nat.mul_le_mul_right _ aa
       _ = A^15 := by ring
       _ = n^(15*p) := by rw [show A^15=n^(p*15) from (pow_mul ..).symm,Nat.mul_comm p]
theorem uniform_live_gate_bound (x : World) (u i : ℕ) (e : ℚ) (he:0<e) (hl:e<1) (hn:2≤x.n) :
    (regionalCircuit x (WindowProfiles.piece x u i) (WindowCSP.scale x u) (WindowCSP.budget (e:ℝ)) (widthBound (e:ℝ))).1.size≤x.n^(75*parameterEnvelope (e:ℝ)) := by
  have realPos:0<(e:ℝ):=by exact_mod_cast he
  have realLt:(e:ℝ)<1:=by exact_mod_cast hl
  have ow:1≤ownerBound (e:ℝ) := by
    unfold ownerBound
    apply Nat.le_floor
    push_cast
    exact (le_div_iff₀ realPos).2 (by linarith)
  apply (integer_gate_count x _ _ _ _ (by omega)).trans
  apply (envelope_power _ _ _ hn).trans
  apply Nat.pow_le_pow_right (by omega)
  have b:WindowCSP.budget (e:ℝ)+1≤5*ownerBound (e:ℝ):=by unfold WindowCSP.budget;omega
  have c:=Nat.mul_le_mul_right (widthBound (e:ℝ)+1) b
  unfold parameterEnvelope
  nlinarith
end StableMSR.Recovery.TightLanguage
namespace StableMSR.Recovery.NativeWriter.Production
open SingleCircuit SingleCodes TightLanguage OracleQueries WindowCSP Relative
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem count_events (s : State) (es : List Event) :
    s.gates.size+es.length≤(es.foldl step s).gates.size+es.count .save := by
  induction es generalizing s with
  | nil=>simp
  | cons e es ih=>
    have h:=ih (step s e)
    cases e <;> simp [step,litStep,sonStep,List.count_cons] at h ⊢ <;> omega

theorem invariant_fold {A B : Type} (J : A→Prop) (xs : List B) (f : A→B→A)
    (h : ∀a b,J a→J (f a b)) (a : A) (ok : J a) : J (xs.foldl f a) := by
  induction xs generalizing a with
  | nil=>exact ok
  | cons b xs ih=>exact ih (f a b) (h a b ok)

theorem unsaved (d : Instance) (w:ℕ) : Event.save ∉ (build (chartAlgebra d) d w).1 := by
  let J:=fun p:List Event×Table ℕ=>Event.save∉p.1
  let K:=fun p:List Event×ℕ=>Event.save∉p.1
  change J _
  unfold build
  apply invariant_fold J _ _ _ _ (by simp [J,chartAlgebra])
  intro p k hp;apply invariant_fold J _ _ _ _ hp
  intro p s hp;apply invariant_fold J _ _ _ _ hp
  intro p c hp;unfold visit;split
  · apply invariant_fold J _ _ _ _ hp
    intro p a hp
    change K (collect (chartAlgebra d) d p.2 c a p.1)
    unfold collect;apply invariant_fold K _ _ _ _ hp
    intro q v hq;apply invariant_fold K _ _ _ _ hq
    intro z x hz
    dsimp only [K,offer];split
    · split
      · simpa [K,chartAlgebra] using hz
      · exact hz
    · exact hz
  · exact hp

theorem chart_saves (d : Instance) (w:ℕ) : (chart d w).1.count .save≤1 := by
  let t:=build (chartAlgebra d) d w
  have h:t.1.count .save=0:=List.count_eq_zero.mpr (unsaved d w)
  unfold chart scan;dsimp only
  generalize hh:(parts d (vertices d)).mapM (m:=Option) (fun c=>TightLanguage.lookup (build (chartAlgebra d) d w).2 c [])=R
  cases R
  case some ids=>
    have hc:(ids.map Event.child).count .save=0 := List.count_eq_zero.mpr (by simp)
    change ((t.1++ids.map Event.child)++[Event.save]).count Event.save≤1
    simp [h,hc]
  case none=>exact Nat.le_trans (Nat.le_of_eq h) (by decide)

theorem chart_length (d : Instance) (w:ℕ) : (chart d w).1.length≤(compileRegion d w).1.size := by
  have sz:=count_events initial (chart d w).1
  have eq:=congrArg (fun p:Gates×ℕ=>p.1.size) (ordered_production_replay d w)
  change (play (chart d w).1).gates.size=(compileRegion d w).1.size at eq
  change 2+(chart d w).1.length≤(play (chart d w).1).gates.size+_ at sz
  have h:=chart_saves d w
  omega

end StableMSR.Recovery.NativeWriter.Production
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open TightLanguage
open OracleQueries SingleCircuit SingleCodes
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem integer_gate_count (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ) (hn : 1 ≤ x.n) :
    (region x W R h w).1.size ≤ gateEnvelope x.n (menuLimit x.n h) x.n w := by
  let K := menuLimit x.n h
  have pos : 0<K := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have words : (SingleCodes.words x.n h).length ≤ K := by
    apply (flat_length _ _ (CartesianBallRows.rows x.n (h+1)) ?_).trans
    · simp [K,menuLimit,CartesianBallRows.rows]
    · intro a ha; simp
  apply circuit_count (arrange (SingleCodes.instanceOf x W R h)) w K x.n pos
  · intro v
    simp only [arrange,Canonical.blockList,List.length_mergeSort,List.length_map,SingleCodes.instanceOf,SingleCodes.lookup]
    split
    · exact (List.length_filter_le ..).trans words
    · simp
  · intro v a
    simp only [arrange,Canonical.blockList,List.length_mergeSort,List.length_map,SingleCodes.instanceOf,SingleCodes.lookup]
    split
    · simp only [SingleCodes.blockList,List.length_map,Finset.length_toList]
      apply (Finset.card_filter_le ..).trans
      apply Finset.card_image_le.trans
      simpa using (Finset.card_le_univ (WindowCSP.window x.dist W R ⟨v,by assumption⟩))
    · simp


theorem uniform_live_gate_bound (x : World) (u i : ℕ) (e : ℚ) (he:0<e) (hl:e<1) (hn:2≤x.n) :
    (region x (WindowProfiles.piece x u i) (WindowCSP.scale x u) (WindowCSP.budget (e:ℝ)) (widthBound (e:ℝ))).1.size≤x.n^(75*parameterEnvelope (e:ℝ)) := by
  have realPos:0<(e:ℝ):=by exact_mod_cast he
  have realLt:(e:ℝ)<1:=by exact_mod_cast hl
  have ow:1≤ownerBound (e:ℝ) := by
    unfold ownerBound
    apply Nat.le_floor
    push_cast
    exact (le_div_iff₀ realPos).2 (by linarith)
  apply (integer_gate_count x _ _ _ _ (by omega)).trans
  apply (envelope_power _ _ _ hn).trans
  apply Nat.pow_le_pow_right (by omega)
  have b:WindowCSP.budget (e:ℝ)+1≤5*ownerBound (e:ℝ):=by unfold WindowCSP.budget;omega
  have c:=Nat.mul_le_mul_right (widthBound (e:ℝ)+1) b
  unfold parameterEnvelope
  nlinarith
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open SingleRAM
open OracleQueries WindowCSP WindowProfiles
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem raw_gate_count (x : World) (h w R M : ℕ)
    (per : ∀ u i, (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.region x (WindowProfiles.piece x u i) (scale x u) h w).1.size ≤ M) :
    (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w R).gates.size ≤ 2+R*M := by
  have step (a : Assembly) (r : ℕ) : (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.appendRegion x h w r a).gates.size ≤ a.gates.size+M := by
    unfold StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.appendRegion
    dsimp only
    split
    · split
      · simp only [Array.size_append,Array.size_map]
        exact Nat.add_le_add_left (per _ _) _
      · exact Nat.le_add_right _ _
    · exact Nat.le_add_right _ _
  have g := TightLanguage.fold_gain (fun a : Assembly => a.gates.size) (List.range R)
    (fun a r => StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.appendRegion x h w r a) emptyAssembly M (fun a r _ => step a r)
  simpa only [StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly,List.length_range,show emptyAssembly.gates.size=2 by rfl] using g

theorem global_assembly_resource_bound (x : World) (e : ℚ)
    (he : 0 < e) (hl : e < 1) (hn : 2 ≤ x.n) :
    let G := (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x (budget (e:ℝ)) (widthBound (e:ℝ))).gates.size
    let A := x.n^(75*parameterEnvelope (e:ℝ))
    G ≤ 2+x.rows*x.n*A ∧
    2+5*(1+3*G*x.n*x.n) ≤ 52*x.cap^4*A ∧
    82+42*G+7*(G*x.n) ≤ 256*x.cap^3*A := by
  let h:=budget (e:ℝ)
  let w:=widthBound (e:ℝ)
  let A:=x.n^(75*parameterEnvelope (e:ℝ))
  let R:=x.rows*x.n
  let G:=(StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x h w).gates.size
  let cp:=x.cap
  have pos:1≤A:=Nat.pow_pos (by omega)
  have raw : (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w R).gates.size ≤ 2+R*A :=
    raw_gate_count _ _ _ _ _ (fun u i => uniform_live_gate_bound x u i e he hl hn)
  have pad : (R+2)/3 ≤ 2+R*A := by
    have lt := Nat.le_mul_of_pos_right R pos
    omega
  have bg : G ≤ 2+R*A := by
    change (padAssembly (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w R) R).gates.size ≤ _
    simp only [padAssembly,Array.size_append,Array.size_replicate]
    omega
  have hp:1≤cp:=by dsimp [cp,World.cap];omega
  have nx:x.n≤cp:=by dsimp [cp,World.cap];omega
  have sx:x.rows≤cp:=by dsimp [cp,World.cap];omega
  have p1 (t : ℕ) : 1≤cp^t*A:=Nat.mul_pos (Nat.pow_pos hp) pos
  have p2:x.n*x.n≤cp^4*A:=by
    calc x.n*x.n ≤ cp*cp := Nat.mul_le_mul nx nx
         _ = cp^2 := by ring
         _ ≤ cp^4 := Nat.pow_le_pow_right hp (by decide)
         _ ≤ _ := Nat.le_mul_of_pos_right _ pos
  have p3:R*x.n*x.n*A≤cp^4*A:=by
    apply Nat.mul_le_mul_right
    calc R*x.n*x.n ≤ cp*cp*cp*cp := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul sx nx) nx) nx
         _ = _ := by ring
  have n3:x.n≤cp^3*A:=by
    calc x.n ≤ cp^1 := by simpa using nx
         _ ≤ cp^3 := Nat.pow_le_pow_right hp (by decide)
         _ ≤ _ := Nat.le_mul_of_pos_right _ pos
  have r3:R*x.n*A ≤ cp^3*A := by
    apply Nat.mul_le_mul_right
    calc R*x.n ≤ cp*cp*cp := Nat.mul_le_mul (Nat.mul_le_mul sx nx) nx
         _ = _ := by ring
  have gg:G*x.n≤2*x.n+R*x.n*A:=by
    calc _ ≤ (2+R*A)*x.n := Nat.mul_le_mul_right _ bg
         _ = _ := by ring
  have g0:G≤G*x.n:=Nat.le_mul_of_pos_right _ (by omega)
  refine ⟨bg,?_,?_⟩
  · change 2+5*(1+3*G*x.n*x.n)≤52*cp^4*A
    calc _ ≤ 2+5*(1+3*(2+R*A)*x.n*x.n) := by gcongr
         _ = 7+30*(x.n*x.n)+15*(R*x.n*x.n*A) := by ring
         _ ≤ 52*(cp^4*A) := by have := p1 4;omega
         _ = _ := by ring
  · change 82+42*G+7*(G*x.n)≤256*cp^3*A
    rw [Nat.mul_assoc 256]
    have := p1 3
    omega

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP BallCoverCatalog
def NativeSpec (e : ℚ) (c D b : ℕ) (cmd : Cmd) : Prop :=
  ∀ (x : World) (s : Store), 1 ≤ x.k → x.k < x.n → IsMetricArray x.dist → Ready x s →
    ∃ t z H, Executes x.dist cmd s t z ∧
      z ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      H ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      let y := worldOf x.k H x.dist t
      Ready y t ∧ y.mem 1 = (x.rows:ℤ) ∧
        let a := Canonical.assembly x (budget (e:ℝ)) (widthBound (e:ℝ))
        1+5*(1+3*a.gates.size*x.n*x.n) < H ∧ SingleRAM.Input y a.gates a.roots

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical

namespace StableMSR.Recovery.CanonicalWriter
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP
set_option autoImplicit false

/-- Address of word i in logical gate column j. -/
def word (j i : ℕ) : ℤ := -(32 + 8*(i:ℤ) + (j:ℤ))

/-- Gate data in gate-major order. Only actual tag, edge, root and bitmap words are prescribed. -/
def Columns (n k S : ℕ) (g : Gates) (roots : ℕ → ℕ) (s : Store) : Prop :=
  s.ptrs 0=(n:ℤ) ∧ s.ptrs 1=(k:ℤ) ∧ s.imem (word 0 0)=(g.size:ℤ) ∧ s.imem (word 0 1)=(S:ℤ) ∧
  (∀ p<g.size, s.imem (word 1 p)=opCode (gateAt g p) ∧
    s.imem (word 2 p)=(leftID (gateAt g p):ℤ) ∧ s.imem (word 3 p)=(rightID (gateAt g p):ℤ)) ∧
  (∀ r<3*g.size, s.imem (word 4 r)=(roots r:ℤ)) ∧
  ∀ p<g.size, ∀ i<n, s.imem (word 5 (p*n+i))=
    (if (tinyMask (gateAt g p)).contains i then 1 else 0)

/-- Uniform computation of the six logical columns of the specified regional assembly. -/
def GeneratesColumns (e : ℚ) (c D b : ℕ) (cmd : Cmd) : Prop :=
  ∀ (x : World) (s : Store), 1 ≤ x.k → x.k < x.n → IsMetricArray x.dist → Ready x s →
    let a := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x (budget (e:ℝ)) (widthBound (e:ℝ))
    ∃ t z, Executes x.dist cmd s t z ∧ z ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      Columns x.n x.k x.rows a.gates a.roots t

end StableMSR.Recovery.CanonicalWriter

namespace StableMSR.Recovery.CanonicalWriter.Encoding
open SingleCircuit SingleRAM
open StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.OracleQueries
set_option autoImplicit false
set_option maxHeartbeats 1500000
def address (k r j : ℕ) := 3+(2*k)*r+j
def fieldValue (g : Gates) (roots : ℕ→ℕ) (r j : ℕ) : ℤ :=
  if r<1+g.size then
    let a:=gateAt g (r-1)
    if j=0 then opCode a else if j=1 then (leftID a:ℤ) else 0
  else if r<1+2*g.size then
    if j=0 then (rightID (gateAt g (r-(1+g.size))):ℤ) else 0
  else if j=0 then (roots (r-(1+2*g.size)):ℤ) else 0
/-- Executable value of each integer cell in the dense target table. -/
def memory (n k S : ℕ) (g : Gates) (roots : ℕ→ℕ) (p : ℕ) : ℤ :=
  let B:=address k (1+5*g.size) 0
  if p=0 then (g.size:ℤ) else if p=1 then (S:ℤ) else if p<B then
    fieldValue g roots ((p-3)/(2*k)) ((p-3)%(2*k))
  else
    let q:=p-B
    if (tinyMask (gateAt g (q/n))).contains (q%n) then 1 else 0
def capacity (n : ℕ) (g : Gates) := 2+5*(1+3*g.size*n*n)
lemma readField (n k S : ℕ) (g : Gates) (roots : ℕ→ℕ)
    {r j : ℕ} (hk : 0<k) (hr : r<1+5*g.size) (hj : j<2*k) :
    memory n k S g roots (address k r j)=fieldValue g roots r j := by
  have h : address k r j<address k (1+5*g.size) 0 := calc
    address k r j < 3+(2*k)*(r+1) := by simp only [address,Nat.mul_add,Nat.mul_one];omega
    _ ≤ address k (1+5*g.size) 0 := by
      unfold address
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  have z : address k r j≠0 := by unfold address;omega
  have o : address k r j≠1 := by unfold address;omega
  unfold memory
  dsimp only
  rw [if_neg z,if_neg o,if_pos h]
  have delta : address k r j-3=(2*k)*r+j := by unfold address;omega
  rw [delta,Nat.mul_add_div (by omega),Nat.div_eq_of_lt hj,Nat.add_zero,Nat.mul_add_mod,Nat.mod_eq_of_lt hj]
private lemma readBit (n k S : ℕ) (g : Gates) (roots : ℕ→ℕ) (p : ℕ) (i : Point n) :
    0< memory n k S g roots (address k (1+5*g.size) 0+p*n+i.val) ↔ i.val∈tinyMask (gateAt g p) := by
  let B:=address k (1+5*g.size) 0
  have Bpos : 3≤B := by dsimp [B,address];omega
  have off : B+p*n+i.val-B=p*n+i.val := by omega
  have div : (p*n+i.val)/n=p := by rw [Nat.mul_comm p n,Nat.mul_add_div (by have:=i.isLt;omega),Nat.div_eq_of_lt i.isLt,Nat.add_zero]
  have rem : (p*n+i.val)%n=i.val := by simp [Nat.add_mod,Nat.mod_eq_of_lt i.isLt]
  change 0< memory n k S g roots (B+p*n+i.val) ↔ _
  unfold memory
  rw [if_neg (by omega),if_neg (by omega),if_neg (show ¬B+p*n+i.val<B by omega),off]
  dsimp only
  rw [div,rem]
  by_cases h:i.val∈tinyMask (gateAt g p) <;> simp [h]
theorem dense_encoding_exact (x : World) (g : Gates) (roots : ℕ→ℕ) (hk : 0<x.k) :
    let H:=capacity x.n g
    let y:={x with rows:=H,mem:=memory x.n x.k x.rows g roots}
    1+5*(1+3*g.size*x.n*x.n)<H ∧ y.mem 1=(x.rows:ℤ) ∧ Input y g roots := by
  let y:={x with rows:=capacity x.n g,mem:=memory x.n x.k x.rows g roots}
  have raw : WindowPorts.rawSize y=g.size := by simp [WindowPorts.rawSize,y,memory]
  have rd (r j : ℕ) (hr:r<1+5*g.size) (hj:j<2*x.k) :
      y.mem (address x.k r j)=fieldValue g roots r j :=readField _ _ _ _ _ hk hr hj
  have addr0 (r : ℕ) : addr x.k r 0=address x.k r 0 := by unfold addr address;ring
  have addr1 (r : ℕ) : addr x.k r 0+1=address x.k r 1 := by rw [addr0]; rfl
  refine ⟨by dsimp [capacity];omega,by simp [y,memory],raw,?_,?_,?_⟩
  · intro p hp
    change y.mem (addr x.k (1+p) 0)=_ ∧ y.mem (addr x.k (1+p) 0+1)=_ ∧ y.mem (addr x.k (1+WindowPorts.rawSize y+p) 0)=_
    rw [raw,addr1,addr0,addr0,rd,rd,rd] <;> try omega
    simp only [fieldValue,if_pos (show 1+p<1+g.size by omega),if_neg (show ¬1+g.size+p<1+g.size by omega),
      if_pos (show 1+g.size+p<1+2*g.size by omega)] 
    simp
  · intro q hq
    change y.mem (addr x.k (1+2*WindowPorts.rawSize y+q) 0)=_
    rw [raw,addr0,rd] <;> try omega
    simp [fieldValue,show ¬1+2*g.size+q<1+g.size by omega,show ¬1+2*g.size+q<1+2*g.size by omega]
  · intro p hp i
    change 0<y.mem (addr x.k (1+5*WindowPorts.rawSize y) 0+p*x.n+i.val) ↔ _
    rw [raw,addr0]
    exact readBit _ _ _ _ _ _ _
end StableMSR.Recovery.CanonicalWriter.Encoding
namespace StableMSR.Recovery.CanonicalWriter.Scatter
open Compiler
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
structure Column where
  start : ℕ
  stride : ℕ
  len : ℕ
def Column.addr (c : Column) (i : ℕ) := c.start+c.stride*i
def header (j f : ℕ) : ℤ := -(1+3*(j:ℤ)+(f:ℤ))
def tape (j i : ℕ) : ℤ := -(32+8*(i:ℤ)+(j:ℤ))
def line : List Op→Cmd | []=>.skip | o::os=>.seq (.atom o) (line os)
noncomputable def perform {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) : List Op→Store
  | []=>s | o::os=>perform d (o.eval d s) os
theorem line_exec {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (ops : List Op) :
    Executes d (line ops) s (perform d s ops) ops.length := by
  induction ops generalizing s with
  | nil=>exact .skip s
  | cons x xs ih=>simpa only [line,perform,List.length_cons,Nat.add_comm 1] using Executes.seq (.atom x s) (ih (x.eval d s))
def initOps (j : ℕ) : List Op :=
  [.pointerConst 9 (header j 0),.integerLoad 4 9,.pointerConst 9 (header j 1),.integerLoad 5 9,
   .pointerConst 9 (header j 2),.integerLoad 6 9,.pointerConst 3 (tape j 0),.pointerConst 7 8,.pointerConst 8 1]
def bodyOps : List Op := [.integerLoad 9 3,.integerStore 4 9,.pointerSub 3 3 7,.pointerAdd 4 4 5,.pointerDec 6]
def copyOne (j : ℕ) := Cmd.seq (line (initOps j)) (.whileDo (.pointerLE 8 6) (line bodyOps))
def copyMany : List ℕ→Cmd | []=>.skip | j::js=>.seq (copyOne j) (copyMany js)
def untouched (a b : Store) := (∀r<3,b.ptrs r=a.ptrs r) ∧ ∀q:ℤ,q<0 → b.imem q=a.imem q
def Has (s : Store) (want : ℕ→ℤ) (j : ℕ) (c : Column) :=
  s.imem (header j 0)=(c.start:ℤ) ∧ s.imem (header j 1)=(c.stride:ℤ) ∧ s.imem (header j 2)=(c.len:ℤ) ∧
    ∀i<c.len,s.imem (tape j i)=want (c.addr i)
theorem has_persists {a b : Store} (u:untouched a b) {want : ℕ→ℤ} {j : ℕ} {c : Column} (h:Has a want j c) : Has b want j c := by
  have H (f : ℕ) : b.imem (header j f)=a.imem (header j f):=u.2 _ (by unfold header;omega)
  exact ⟨(H 0).trans h.1,(H 1).trans h.2.1,(H 2).trans h.2.2.1,fun i hi=>(u.2 _ (by unfold tape;omega)).trans (h.2.2.2 i hi)⟩
def Filled (b s : Store) (want : ℕ→ℤ) (c : Column) (i : ℕ) :=
  ∀p : ℕ,b.imem (p:ℤ)=want p ∨ (∃l < i,c.addr l=p) → s.imem (p:ℤ)=want p
structure At (base s : Store) (want : ℕ→ℤ) (j : ℕ) (c : Column) (i m : ℕ) : Prop where
  source : s.ptrs 3=tape j i
  dest : s.ptrs 4=(c.addr i:ℤ)
  stride : s.ptrs 5=(c.stride:ℤ)
  remain : s.ptrs 6=(m:ℤ)
  eight : s.ptrs 7=8
  one : s.ptrs 8=1
  keep : untouched base s
  filled : Filled base s want c i
theorem initial {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (want : ℕ→ℤ) (j : ℕ) (c : Column) (h:Has s want j c) :
    At s (perform d s (initOps j)) want j c 0 c.len := by
  obtain ⟨h0,h1,h2,hv⟩:=h
  constructor
  · simp [perform,initOps,Op.eval]
  · simp [perform,initOps,Op.eval,Column.addr,h0]
  · simp [perform,initOps,Op.eval,h1]
  · simp [perform,initOps,Op.eval,h2]
  · simp [perform,initOps,Op.eval]
  · simp [perform,initOps,Op.eval]
  · constructor
    · intro r hr;interval_cases r <;> simp [perform,initOps,Op.eval,Function.update]
    · intro q hq;rfl
  · intro p h;rcases h with h|⟨l,hl,_⟩
    · exact h
    · omega
theorem advance {n : ℕ} (d : Point n→Point n→ℝ) {base s : Store} {want : ℕ→ℤ} {j : ℕ} {c : Column} {i m : ℕ}
    (src:Has base want j c) (hi:i<c.len) (h:At base s want j c i (m+1)) :
    At base (perform d s bodyOps) want j c (i+1) m := by
  let t:=perform d s bodyOps
  have val:s.imem (s.ptrs 3)=want (c.addr i):=by
    rw [h.source,h.keep.2 _ (by unfold tape;omega),src.2.2.2 i hi]
  have mem (p : ℤ) : t.imem p=if p=(c.addr i:ℤ) then want (c.addr i) else s.imem p := by
    simp [t,perform,bodyOps,Op.eval,Function.update,h.dest,val]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [perform,bodyOps,Op.eval,h.source,h.eight,tape];ring
  · simp [perform,bodyOps,Op.eval,h.dest,h.stride,Column.addr,Nat.mul_add,add_assoc]
  · simpa [perform,bodyOps,Op.eval] using h.stride
  · simp [perform,bodyOps,Op.eval,h.remain]
  · simpa [perform,bodyOps,Op.eval] using h.eight
  · simpa [perform,bodyOps,Op.eval] using h.one
  · constructor
    · intro r hr;interval_cases r <;> simpa [perform,bodyOps,Op.eval,Function.update] using h.keep.1 _ (by decide)
    · intro q hq;rw [mem,if_neg (by omega)];exact h.keep.2 _ hq
  · intro p hp
    rw [mem];by_cases e:p=c.addr i
    · subst p;simp
    · rw [if_neg (by exact_mod_cast e)]
      apply h.filled
      rcases hp with hz|⟨k,hk,eq⟩
      · exact Or.inl hz
      · have ne : k≠i := by rintro rfl;exact e eq.symm
        exact Or.inr ⟨k,by omega,eq⟩
theorem while_exec {n : ℕ} (d : Point n→Point n→ℝ) {base : Store} {want : ℕ→ℤ} {j : ℕ} {c : Column}
    (src:Has base want j c) (m i : ℕ) (endAt:i+m=c.len) (s : Store) (h:At base s want j c i m) :
    ∃t,Executes d (.whileDo (.pointerLE 8 6) (line bodyOps)) s t (7*m+2) ∧ At base t want j c (i+m) 0 := by
  induction m generalizing i s with
  | zero=>
    exact ⟨s,.while_false (by change ¬s.ptrs 8 ≤ s.ptrs 6;rw [h.one,h.remain];decide),by simpa using h⟩
  | succ m ih=>
    let t:=perform d s bodyOps
    have a:=advance d src (by omega) h
    obtain ⟨z,go,last⟩:=ih (i+1) (by omega) t a
    have yes : (Cond.pointerLE 8 6).test s := by change s.ptrs 8 ≤ s.ptrs 6;rw [h.one,h.remain];omega
    have step:=Executes.while_true yes (line_exec d s bodyOps) go
    exact ⟨z,by simpa only [show 1+bodyOps.length+1+(7*m+2)=7*(m+1)+2 by change 1+5+1+(7*m+2)=_;omega] using step,by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using last⟩
theorem one_exec {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (want : ℕ→ℤ) (j : ℕ) (c : Column) (h:Has s want j c) :
    ∃t,Executes d (copyOne j) s t (11+7*c.len) ∧ untouched s t ∧ Filled s t want c c.len := by
  have a:=initial d s want j c h
  obtain ⟨t,go,u⟩:=while_exec d h c.len 0 (by simp) _ a
  refine ⟨t,?_,u.keep,by simpa using u.filled⟩
  have p:=Executes.seq (line_exec d s (initOps j)) go
  simpa only [copyOne,show (initOps j).length+(7*c.len+2)=11+7*c.len by change 9+_=11+_;omega] using p
theorem many_exec {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (cols : ℕ → Column) (want : ℕ→ℤ) (js : List ℕ)
    (all : ∀j∈js,Has s want j (cols j)) :
    ∃t,Executes d (copyMany js) s t ((js.map (fun j=>11+7*(cols j).len)).sum) ∧ untouched s t ∧
    ∀p:ℕ,s.imem (p:ℤ)=want p ∨ (∃j∈js,∃i<(cols j).len,(cols j).addr i=p) → t.imem (p:ℤ)=want p := by
  induction js generalizing s with
  | nil=>exact ⟨s,.skip s,⟨fun _ _=>rfl,fun _ _=>rfl⟩,fun p h=>by simpa using h⟩
  | cons j js ih=>
    obtain ⟨t,one,ut,ft⟩:=one_exec d s want j _ (all j (by simp))
    obtain ⟨z,go,uz,fz⟩:=ih t (fun k hk=>has_persists ut (all k (by simp [hk])))
    refine ⟨z,.seq one go,⟨fun r hr=>(uz.1 r hr).trans (ut.1 r hr),fun q hq=>(uz.2 q hq).trans (ut.2 q hq)⟩,?_⟩
    intro p h;apply fz
    rcases h with h|⟨k,hk,i,hi,eq⟩
    · exact Or.inl (ft p (Or.inl h))
    · rcases List.mem_cons.mp hk with rfl|hm
      · exact Or.inl (ft p (Or.inr ⟨i,hi,eq⟩))
      · exact Or.inr ⟨k,hm,i,hi,eq⟩
end StableMSR.Recovery.CanonicalWriter.Scatter

/-! The six physical columns, the exact native execution time, and the dense input contract. -/

namespace StableMSR.Recovery.CanonicalWriter.Scatter
open Compiler OracleQueries SingleCircuit SingleRAM BallCoverCatalog
set_option autoImplicit false
set_option maxHeartbeats 1600000
def columns (n k g : ℕ) : ℕ → Column
  | 0=>⟨0,1,2⟩
  | 1=>⟨addr k 1 0,2*k,g⟩
  | 2=>⟨addr k 1 0+1,2*k,g⟩
  | 3=>⟨addr k (1+g) 0,2*k,g⟩
  | 4=>⟨addr k (1+2*g) 0,2*k,3*g⟩
  | _=>⟨addr k (1+5*g) 0,1,g*n⟩
def jobs : List ℕ := [0,1,2,3,4,5]
def lastOps : List Op := [.pointerConst 9 (-24),.integerLoad 2 9]
def format := Cmd.seq (copyMany jobs) (line lastOps)
def Packed (n k S : ℕ) (g : Gates) (roots : ℕ→ℕ) (s : Store) :=
  s.ptrs 0=(n:ℤ) ∧ s.ptrs 1=(k:ℤ) ∧ s.imem (-24)=(Encoding.capacity n g:ℤ) ∧
  ∀j∈jobs, Has s (Encoding.memory n k S g roots) j (columns n k g.size j)
theorem format_exec {n : ℕ} (d : Point n→Point n→ℝ) (k S : ℕ) (g : Gates) (roots : ℕ→ℕ) (s : Store)
    (hk : 0<k) (pk:Packed n k S g roots s) :
    ∃t,Executes d format s t (82+42*g.size+7*(g.size*n)) ∧
      let y:=worldOf k (Encoding.capacity n g) d t
      Ready y t ∧ y.mem 1=(S:ℤ) ∧ Input y g roots := by
  let cs:=columns n k g.size
  let want:=Encoding.memory n k S g roots
  obtain ⟨v,go,uv,fill⟩:=many_exec d s cs want jobs pk.2.2.2
  let t:=perform d v lastOps
  let y:=worldOf k (Encoding.capacity n g) d t
  let z : World:=⟨n,k,Encoding.capacity n g,d,want⟩
  have act:=Executes.seq go (line_exec d v lastOps)
  refine ⟨t,?_,?_,?_,?_⟩
  · have tm:(jobs.map (fun j=>11+7*(cs j).len)).sum+lastOps.length=82+42*g.size+7*(g.size*n) := by
      simp [jobs,cs,columns,lastOps,List.sum_cons] <;> ring
    simpa only [format,t,tm] using act
  · constructor
    · intro a;cases a with
      | points=>exact (uv.1 0 (by decide)).trans pk.1
      | blocks=>exact (uv.1 1 (by decide)).trans pk.2.1
      | rows=>change (perform d v lastOps).ptrs 2=(Encoding.capacity n g:ℤ);simpa [perform,lastOps,Op.eval] using (uv.2 (-24) (by decide)).trans pk.2.2.1
    · intro p;rfl
  · have h:=fill 1 (Or.inr ⟨0,by decide,1,by change 1<2;decide,rfl⟩)
    change v.imem (1:ℤ)=_;simpa [want,Encoding.memory] using h
  · have cell (j : ℕ) (hj:j∈jobs) (i : ℕ) (hi:i<(cs j).len) : y.mem ((cs j).addr i)=z.mem ((cs j).addr i) := fill _ (Or.inr ⟨j,hj,i,hi,rfl⟩)
    let x : World:=⟨n,k,S,d,want⟩
    have exactZ : Input z g roots := (Encoding.dense_encoding_exact x g roots hk).2.2
    have rawY:WindowPorts.rawSize y=g.size:=by
      have h:=cell 0 (by decide) 0 (by change 0<2;decide)
      change y.mem 0=want 0 at h
      unfold WindowPorts.rawSize;rw [h];simp [want,Encoding.memory]
    have tag (p : ℕ) : (cs 1).addr p=addr k (1+p) 0 := by dsimp [cs,columns,Column.addr,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    have left (p : ℕ) : (cs 2).addr p=addr k (1+p) 0+1 := by dsimp [cs,columns,Column.addr,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    have right (p : ℕ) : (cs 3).addr p=addr k (1+g.size+p) 0 := by dsimp [cs,columns,Column.addr,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    have root (p : ℕ) : (cs 4).addr p=addr k (1+2*g.size+p) 0 := by dsimp [cs,columns,Column.addr,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
    have bit (p : ℕ) : (cs 5).addr p=addr k (1+5*g.size) 0+p := by simp [cs,columns,Column.addr]
    refine ⟨rawY,?_,?_,?_⟩
    · intro p hp
      have h1:=cell 1 (by decide) p hp;rw [tag] at h1
      have h2:=cell 2 (by decide) p hp;rw [left] at h2
      have h3:=cell 3 (by decide) p hp;rw [right] at h3
      have info:=exactZ.2.1 p hp
      change z.mem (addr k (1+p) 0)=_ ∧ z.mem (addr k (1+p) 0+1)=_ ∧ z.mem (addr k (1+WindowPorts.rawSize z+p) 0)=_ at info
      rw [exactZ.1] at info
      change y.mem (addr k (1+p) 0)=_ ∧ y.mem (addr k (1+p) 0+1)=_ ∧ y.mem (addr k (1+WindowPorts.rawSize y+p) 0)=_
      rw [rawY,h1,h2,h3];exact info
    · intro p hp;have h:=cell 4 (by decide) p hp;rw [root] at h
      have zt:=exactZ.2.2.1 p hp
      change z.mem (addr k (1+2*WindowPorts.rawSize z+p) 0)=_ at zt
      change y.mem (addr k (1+2*WindowPorts.rawSize y+p) 0)=_
      rw [exactZ.1] at zt;rw [rawY,h];exact zt
    · intro p hp i
      have bound:p*n+i.val<g.size*n:=by
        have le:=Nat.mul_le_mul_right n (show p+1≤g.size by omega)
        rw [Nat.add_mul,one_mul] at le;have hi:i.val<n:=i.isLt;omega
      have h:=cell 5 (by decide) (p*n+i.val) bound;rw [bit,←Nat.add_assoc] at h
      have zt:=exactZ.2.2.2 p hp i
      change (0<z.mem (addr k (1+5*WindowPorts.rawSize z) 0+p*n+i.val)) ↔ _ at zt
      change (0<y.mem (addr k (1+5*WindowPorts.rawSize y) 0+p*n+i.val)) ↔ _
      rw [exactZ.1] at zt;rw [rawY,h];exact zt
end StableMSR.Recovery.CanonicalWriter.Scatter

/-! The scratch tape words are exactly the logical gate data. -/

namespace StableMSR.Recovery.CanonicalWriter.Scatter
open Compiler SingleCircuit SingleRAM BallCoverCatalog
set_option autoImplicit false
set_option maxHeartbeats 1500000
/-- Logical scratch columns, in copy order. A bitmap index ranges over gate-major, point-minor order. -/
def datum (n S : ℕ) (g : Gates) (roots : ℕ→ℕ) : ℕ→ℕ→ℤ
  | 0,i=>if i=0 then (g.size:ℤ) else (S:ℤ)
  | 1,i=>opCode (gateAt g i)
  | 2,i=>(leftID (gateAt g i):ℤ)
  | 3,i=>(rightID (gateAt g i):ℤ)
  | 4,i=>(roots i:ℤ)
  | _,i=>if (tinyMask (gateAt g (i/n))).contains (i%n) then 1 else 0
theorem column_contents (n k S : ℕ) (hk:0<k) (g : Gates) (roots : ℕ→ℕ) (j : ℕ) (hj:j∈jobs)
    (i : ℕ) (hi:i<(columns n k g.size j).len) :
    Encoding.memory n k S g roots ((columns n k g.size j).addr i)=datum n S g roots j i := by
  have jj:j<6:=by simp [jobs] at hj;omega
  interval_cases j
  · change i<2 at hi
    interval_cases i <;> simp [columns,Column.addr,datum,Encoding.memory]
  · change i<g.size at hi
    have loc:(columns n k g.size 1).addr i=Encoding.address k (1+i) 0 := by
      dsimp [columns,Column.addr,Encoding.address,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [loc,Encoding.readField _ _ _ _ _ hk (by omega) (by omega)]
    simp [datum,Encoding.fieldValue,show 1+i<1+g.size by omega]
  · change i<g.size at hi
    have loc:(columns n k g.size 2).addr i=Encoding.address k (1+i) 1 := by
      dsimp [columns,Column.addr,Encoding.address,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [loc,Encoding.readField _ _ _ _ _ hk (by omega) (by omega)]
    simp [datum,Encoding.fieldValue,show 1+i<1+g.size by omega]
  · change i<g.size at hi
    have loc:(columns n k g.size 3).addr i=Encoding.address k (1+g.size+i) 0 := by
      dsimp [columns,Column.addr,Encoding.address,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [loc,Encoding.readField _ _ _ _ _ hk (by omega) (by omega)]
    simp [datum,Encoding.fieldValue,show ¬1+g.size+i<1+g.size by omega,show 1+g.size+i<1+2*g.size by omega]
  · change i<3*g.size at hi
    have loc:(columns n k g.size 4).addr i=Encoding.address k (1+2*g.size+i) 0 := by
      dsimp [columns,Column.addr,Encoding.address,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    rw [loc,Encoding.readField _ _ _ _ _ hk (by omega) (by omega)]
    simp [datum,Encoding.fieldValue,show ¬1+2*g.size+i<1+g.size by omega,show ¬1+2*g.size+i<1+2*g.size by omega]
  · let B:=Encoding.address k (1+5*g.size) 0
    have loc:(columns n k g.size 5).addr i=B+i := by
      dsimp [columns,Column.addr,B,Encoding.address,addr];ring <;> simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
    have hb:3≤B:=by dsimp [B,Encoding.address];omega
    rw [loc]
    change (if B+i=0 then _ else if B+i=1 then _ else if B+i<B then _ else _) = _
    simp only [if_neg (show B+i≠0 by omega),if_neg (show B+i≠1 by omega),if_neg (show ¬B+i<B by omega)]
    change (if (tinyMask (gateAt g ((B+i-B)/n))).contains ((B+i-B)%n) then (1:ℤ) else 0)=_
    rw [Nat.add_sub_cancel_left];rfl
theorem packed_iff_gate_data (n k S : ℕ) (hk:0<k) (g : Gates) (roots : ℕ→ℕ) (s : Store) :
    Packed n k S g roots s ↔ s.ptrs 0=(n:ℤ) ∧ s.ptrs 1=(k:ℤ) ∧ s.imem (-24)=(Encoding.capacity n g:ℤ) ∧
      ∀j∈jobs,let c:=columns n k g.size j
      s.imem (header j 0)=(c.start:ℤ) ∧ s.imem (header j 1)=(c.stride:ℤ) ∧ s.imem (header j 2)=(c.len:ℤ) ∧
      ∀i<c.len,s.imem (tape j i)=datum n S g roots j i := by
  unfold Packed Has
  apply and_congr_right;intro _
  apply and_congr_right;intro _
  apply and_congr_right;intro _
  apply forall_congr';intro j
  apply forall_congr';intro hj
  dsimp only
  apply and_congr_right;intro _
  apply and_congr_right;intro _
  apply and_congr_right;intro _
  apply forall_congr';intro i
  apply forall_congr';intro hi
  rw [column_contents n k S hk g roots j hj i hi]
end StableMSR.Recovery.CanonicalWriter.Scatter

namespace StableMSR.Recovery.CanonicalWriter.Header
open Compiler Scatter
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Registers below b and all integer memory survive evaluation of a header expression. -/
def Frame (b : ℕ) (s t : Store) := (∀ i<b, t.ptrs i=s.ptrs i) ∧ t.imem=s.imem
theorem frame_trans {b : ℕ} {s t u : Store} (h : Frame b s t) (v : Frame b t u) : Frame b s u :=
  ⟨fun i hi => (v.1 i hi).trans (h.1 i hi),v.2.trans h.2⟩

def addBody (b : ℕ) : List Op := [.pointerAdd b b (b+1),.pointerDec (b+2)]
def addLoop (b : ℕ) : Cmd := .whileDo (.pointerLE (b+3) (b+2)) (line (addBody b))

theorem addLoop_run {n : ℕ} (d : Point n→Point n→ℝ) (b m : ℕ) (s : Store) (a v : ℤ)
    (ha : s.ptrs b=a) (hv : s.ptrs (b+1)=v) (hm : s.ptrs (b+2)=(m:ℤ)) (ho : s.ptrs (b+3)=1) :
    ∃ t, Executes d (addLoop b) s t (2+4*m) ∧ Frame b s t ∧ t.ptrs b=a+(m:ℤ)*v := by
  induction m generalizing s a with
  | zero =>
    refine ⟨s,Executes.while_false ?_,⟨fun _ _=>rfl,rfl⟩,by simpa using ha⟩
    change ¬ s.ptrs (b+3) ≤ s.ptrs (b+2)
    rw [ho,hm];decide
  | succ m ih =>
    let t:=perform d s (addBody b)
    have ht : Frame b s t := by
      refine ⟨?_,rfl⟩;intro i hi
      simp [t,perform,addBody,Op.eval,Function.update_of_ne (by omega : i≠b+2),Function.update_of_ne (by omega : i≠b)]
    obtain ⟨u,go,hu,final⟩:=ih t (a+v) (by simp [t,perform,addBody,Op.eval,ha,hv])
      (by simp [t,perform,addBody,Op.eval,hv]) (by simp [t,perform,addBody,Op.eval,hm])
      (by simp [t,perform,addBody,Op.eval,ho])
    have yes : (Cond.pointerLE (b+3) (b+2)).test s := by change s.ptrs _ ≤ s.ptrs _;rw [ho,hm];omega
    have all:=Executes.while_true yes (line_exec d s (addBody b)) go
    refine ⟨u,?_,frame_trans ht hu,?_⟩
    · simpa only [addLoop,show 1+(addBody b).length+1+(2+4*m)=2+4*(m+1) by change 1+2+1+_= _;omega] using all
    · rw [final];push_cast;ring

/-- Nonnegative header arithmetic. Only the point and block dimensions occur as loop bounds. -/
inductive Term where
  | num (c : ℕ) | n | k | g | plus (a b : Term) | scale (points : Bool) (a : Term)
def Term.val (n k g : ℕ) : Term → ℕ
  | .num c=>c | .n=>n | .k=>k | .g=>g
  | .plus a b=>a.val n k g+b.val n k g
  | .scale points a=>a.val n k g*(if points then n else k)
def Term.weight : Term → ℕ
  | .plus a b=>a.weight+b.weight+1
  | .scale _ a=>a.weight+10
  | _=>1
def setup (b : ℕ) (points : Bool) : List Op :=
  [.pointerCopy (b+1) b,.pointerConst b 0,.pointerCopy (b+2) (if points then 0 else 1),.pointerConst (b+3) 1]
def Term.code : Term → ℕ → Cmd
  | .num c,b=>.atom (.pointerConst b c)
  | .n,b=>.atom (.pointerCopy b 0) | .k,b=>.atom (.pointerCopy b 1) | .g,b=>.atom (.pointerCopy b 3)
  | .plus a t,b=>.seq (a.code b) (.seq (t.code (b+1)) (.atom (.pointerAdd b b (b+1))))
  | .scale flag a,b=>.seq (a.code b) (.seq (line (setup b flag)) (addLoop b))

def Args (n k g : ℕ) (s : Store) := s.ptrs 0=(n:ℤ) ∧ s.ptrs 1=(k:ℤ) ∧ s.ptrs 3=(g:ℤ)
theorem args_frame {n k g b : ℕ} {s t : Store} (hb : 4≤b) (args : Args n k g s) (h : Frame b s t) : Args n k g t :=
  ⟨(h.1 0 (by omega)).trans args.1,(h.1 1 (by omega)).trans args.2.1,(h.1 3 (by omega)).trans args.2.2⟩

theorem term_run {n : ℕ} (d : Point n→Point n→ℝ) (k g : ℕ) (a : Term) (b : ℕ) (hb : 4≤b)
    (s : Store) (args : Args n k g s) :
    ∃ t z, Executes d (a.code b) s t z ∧ Frame b s t ∧ t.ptrs b=(a.val n k g:ℤ) ∧
      z ≤ a.weight*(1+n+k) := by
  induction a generalizing b s with
  | num c | n | k | g =>
    all_goals refine ⟨_,1,.atom _ _,⟨?_,rfl⟩,?_,?_⟩
    all_goals first
      | intro i hi; simp [Op.eval,Function.update_of_ne (by omega : i≠b)]
      | solve | simp [Term.val,Op.eval,args.1,args.2.1,args.2.2]
      | simp [Term.weight] <;> omega
  | plus a t ha ht =>
    obtain ⟨u,za,ea,fa,va,ta⟩:=ha b hb s args
    obtain ⟨v,zc,ec,fc,vc,tc⟩:=ht (b+1) (by omega) u (args_frame hb args fa)
    let op:=Op.pointerAdd b b (b+1)
    let l:=op.eval d v
    refine ⟨l,za+(zc+1),.seq ea (.seq ec (.atom op v)),⟨?_,fc.2.trans fa.2⟩,?_,?_⟩
    · intro i hi
      simpa [l,op,Op.eval,Function.update_of_ne (by omega : i≠b)] using (fc.1 i (by omega)).trans (fa.1 i hi)
    · simp [l,op,Op.eval,Term.val,fc.1 b (by omega),va,vc]
    · simp only [Term.weight,Nat.add_mul,Nat.one_mul];omega
  | scale flag a ih =>
    obtain ⟨u,z,go,fr,val,cost⟩:=ih b hb s args
    let m:=if flag then n else k
    let v:=perform d u (setup b flag)
    have au:=args_frame hb args fr
    have start : Frame b u v := by
      refine ⟨?_,rfl⟩;intro i hi
      simp [v,perform,setup,Op.eval,Function.update_of_ne (by omega : i≠b+3),
        Function.update_of_ne (by omega : i≠b+2),Function.update_of_ne (by omega : i≠b+1),Function.update_of_ne (by omega : i≠b)]
    have reg : v.ptrs (b+2)=(m:ℤ) := by
      have i0:0≠b:=by omega
      have i1:1≠b:=by omega
      cases flag <;> simp [v,m,perform,setup,Op.eval,i0,i1,Function.update_of_ne (by omega : 1≠b+1),au.1,au.2.1]
    obtain ⟨t,loop,ft,out⟩:=addLoop_run d b m v 0 (a.val n k g:ℤ)
      (by simp [v,perform,setup,Op.eval]) (by simp [v,perform,setup,Op.eval,val]) reg (by simp [v,perform,setup,Op.eval])
    refine ⟨t,z+((setup b flag).length+(2+4*m)),.seq go (.seq (line_exec d u _) loop),frame_trans fr (frame_trans start ft),?_,?_⟩
    · cases flag <;> simpa [Term.val,m,mul_comm] using out
    · have bound : m≤n+k := by cases flag <;> simp [m] <;> omega
      change z+(4+(2+4*m))≤(a.weight+10)*(1+n+k)
      rw [Nat.add_mul];omega

end StableMSR.Recovery.CanonicalWriter.Header

namespace StableMSR.Recovery.CanonicalWriter.Header
open Compiler Scatter SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 14000

def copies : ℕ → Term → Term
  | 0,_=>.num 0
  | m+1,a=>.plus (copies m a) a
@[simp] theorem copies_val (m n k g : ℕ) (a : Term) : (copies m a).val n k g=m*a.val n k g := by
  induction m <;> simp [copies,Term.val, *, Nat.succ_mul]
def record (m : ℕ) : Term := .plus (.num 3) (copies 2 (.scale false (.plus (.num 1) (copies m .g))))
def descriptor : ℕ → ℕ → Term
  | 0,0=>.num 0 | 0,1=>.num 1 | 0,_=>.num 2
  | 1,0=>record 0 | 2,0=>.plus (record 0) (.num 1)
  | 3,0=>record 1 | 4,0=>record 2 | _,0=>record 5
  | 5,1=>.num 1 | _,1=>copies 2 .k
  | 4,_=>copies 3 .g | 5,_=>.scale true .g | _,_=>.g
def expression (i : ℕ) : Term :=
  if i=23 then .plus (.num 7) (copies 15 (.scale true (.scale true .g))) else descriptor (i/3) (i%3)
def cell (i : ℕ) : ℤ := -(1+(i:ℤ))
def tailOps (i : ℕ) : List Op := [.pointerConst 5 (cell i),.integerStore 5 4]
def writeOne (i : ℕ) : Cmd := .seq ((expression i).code 4) (line (tailOps i))
def writeList : List ℕ → Cmd | []=>.skip | i::is=>.seq (writeOne i) (writeList is)
def totalWeight (is : List ℕ) := (is.map (fun i => (expression i).weight+2)).sum
def loadSize : List Op := [.pointerConst 4 (word 0 0),.integerLoad 3 4]
def prepare : Cmd := .seq (line loadSize) (writeList (List.range 24))
def overhead : ℕ := totalWeight (List.range 24)+2

theorem list_run {n : ℕ} (d : Point n→Point n→ℝ) (k g : ℕ) (is : List ℕ) (s : Store)
    (args : Args n k g s) (small : ∀ i ∈ is, i<24) :
    ∃ t z, Executes d (writeList is) s t z ∧ z ≤ totalWeight is*(1+n+k) ∧ Args n k g t ∧
      (∀q:ℤ, q≤ -32 → t.imem q=s.imem q) ∧
      ∀ j, s.imem (cell j)=((expression j).val n k g:ℤ) ∨ j∈is →
        t.imem (cell j)=((expression j).val n k g:ℤ) := by
  induction is generalizing s with
  | nil => exact ⟨s,0,.skip _,by simp [totalWeight],args,fun _ _=>rfl,fun _ h=>by simpa using h⟩
  | cons i is ih =>
    obtain ⟨u,zu,go,fr,val,tm⟩:=term_run d k g (expression i) 4 (by decide) s args
    let v:=perform d u (tailOps i)
    have mv (q : ℤ) : v.imem q = if q=cell i then ((expression i).val n k g:ℤ) else s.imem q := by
      simp [v,perform,tailOps,Op.eval,Function.update_apply,val,fr.2]
    have av : Args n k g v := by
      obtain ⟨a,b,c⟩:=args_frame (by decide) args fr
      exact ⟨by simpa [v,perform,tailOps,Op.eval] using a,
        by simpa [v,perform,tailOps,Op.eval] using b,by simpa [v,perform,tailOps,Op.eval] using c⟩
    obtain ⟨t,z,gt,tt,at',bt,all⟩:=ih v av (fun j hj=>small j (by simp [hj]))
    refine ⟨t,(zu+(tailOps i).length)+z,.seq (.seq go (line_exec d u _)) gt,?_,at',?_,?_⟩
    · have ws : totalWeight (i::is)=((expression i).weight+2)+totalWeight is := by simp [totalWeight]
      rw [ws,Nat.add_mul,Nat.add_mul]
      change (zu+2)+z ≤ _
      omega
    · intro q hq;rw [bt q hq,mv,if_neg]
      have hi:=small i (by simp);unfold cell;omega
    · intro j hj;apply all
      by_cases eq:j=i
      · subst j;left;simp [mv]
      · rcases hj with e|e
        · left;rw [mv,if_neg];exact e
          unfold cell;omega
        · right;simpa [eq] using e

theorem descriptor_val (n k g j f : ℕ) (hj : j<6) (hf : f<3) :
    (descriptor j f).val n k g =
      if f=0 then (columns n k g j).start else if f=1 then (columns n k g j).stride else (columns n k g j).len := by
  interval_cases j <;> interval_cases f <;>
    simp [descriptor,record,Term.val,columns,BallCoverCatalog.addr] <;> ring

theorem prepare_run {n : ℕ} (d : Point n→Point n→ℝ) (k S : ℕ) (g : Gates) (roots : ℕ→ℕ) (s : Store)
    (hk : 0<k) (h : Columns n k S g roots s) :
    ∃ t z, Executes d prepare s t z ∧ z≤overhead*(1+n+k) ∧ Packed n k S g roots t := by
  obtain ⟨sn,sk,cnt,rows,gate,root,bit⟩:=h
  let u:=perform d s loadSize
  have a : Args n k g.size u := by
    exact ⟨by simpa [u,perform,loadSize,Op.eval] using sn,by simpa [u,perform,loadSize,Op.eval] using sk,
      by simpa [u,perform,loadSize,Op.eval] using cnt⟩
  obtain ⟨t,z,go,cost,args,keep,cols⟩:=list_run d k g.size (List.range 24) u a (fun i hi=>List.mem_range.mp hi)
  refine ⟨t,loadSize.length+z,.seq (line_exec d s _) go,?_,?_⟩
  · change 2+z ≤ (totalWeight (List.range 24)+2)*(1+n+k)
    rw [Nat.add_mul];omega
  · apply (packed_iff_gate_data n k S hk g roots t).2
    have get (j : ℕ) (hj : j<24) := cols j (Or.inr (List.mem_range.mpr hj))
    have cap := get 23 (by decide)
    have eq : (expression 23).val n k g.size=Encoding.capacity n g := by simp [expression,Term.val,Encoding.capacity];ring
    rw [eq] at cap
    refine ⟨args.1,args.2.1,cap,?_⟩
    intro j hj
    have jj:j<6:=by simp [jobs] at hj;omega
    have hd (f : ℕ) (hf : f<3) : t.imem (header j f)=
        ((if f=0 then (columns n k g.size j).start else if f=1 then (columns n k g.size j).stride else (columns n k g.size j).len:ℕ):ℤ) := by
      have z:=get (3*j+f) (by omega)
      have ce : cell (3*j+f)=header j f := by simp [cell,header];ring
      have ex : expression (3*j+f)=descriptor j f := by
        unfold expression
        rw [if_neg (by omega),show (3*j+f)/3=j by omega,show (3*j+f)%3=f by omega]
      rwa [ce,ex,descriptor_val _ _ _ _ _ jj hf] at z
    refine ⟨by simpa using hd 0 (by decide),by simpa using hd 1 (by decide),by simpa using hd 2 (by decide),?_⟩
    intro i hi
    have hold : t.imem (tape j i)=s.imem (word j i) := keep _ (by unfold tape;omega)
    rw [hold]
    interval_cases j
    · change i<2 at hi
      interval_cases i
      · exact cnt
      · exact rows
    · exact (gate i hi).1
    · exact (gate i hi).2.1
    · exact (gate i hi).2.2
    · exact root i hi
    · change i<g.size*n at hi
      have nn:0<n:=by by_contra! e;simp [show n=0 by omega] at hi
      have p : i/n<g.size := (Nat.div_lt_iff_lt_mul nn).2 hi
      have b:=bit _ p _ (Nat.mod_lt i nn)
      rwa [Nat.mul_comm (i/n) n, Nat.div_add_mod i n] at b

end StableMSR.Recovery.CanonicalWriter.Header

namespace StableMSR.Recovery.CanonicalWriter
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem writer_of_columns
    (source : ∃ c D b : ℕ, ∀ e : ℚ, 0 < e → e < 1 → ∃ cmd : Cmd, GeneratesColumns e c D b cmd) :
    ∃ c D b : ℕ, 0<c ∧ 0<b ∧ ∀ e : ℚ, 0<e → e<1 → ∃ cmd : Cmd, StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.NativeSpec e c D b cmd := by
  obtain ⟨c,D,b,src⟩:=source
  refine ⟨c+Header.overhead+256,D+4,b+75,by omega,by omega,?_⟩
  intro e he hl
  obtain ⟨p,P⟩:=src e he hl
  refine ⟨.seq p (.seq Header.prepare Scatter.format),?_⟩
  intro x s hk kn metric ready
  let a:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x (budget (e:ℝ)) (widthBound (e:ℝ))
  let E:=parameterEnvelope (e:ℝ)
  let L:=x.cap^(D+4)*x.n^((b+75)*E)
  have nn:2≤x.n:=by omega
  have cp:1≤x.cap:=by dsimp [World.cap];omega
  have mono (j t : ℕ) (j0 : j≤D+4) (t0 : t≤b+75) : x.cap^j*x.n^(t*E) ≤ L :=
    Nat.mul_le_mul (Nat.pow_le_pow_right cp j0) (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ t0))
  obtain ⟨u,z,run,time,cols⟩:=P x s hk kn metric ready
  obtain ⟨v,h,head,ht,pk⟩:=Header.prepare_run x.dist x.k x.rows a.gates a.roots u hk cols
  obtain ⟨t,out,fields⟩:=Scatter.format_exec x.dist x.k x.rows a.gates a.roots v hk pk
  let f:=82+42*a.gates.size+7*(a.gates.size*x.n)
  have resources:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.global_assembly_resource_bound x e he hl nn
  have time' : z≤c*L:=by
    apply time.trans
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c (mono D b (by omega) (by omega))
  have hh : h≤Header.overhead*L:=by
    have d : 1+x.n+x.k≤x.cap:=by dsimp [World.cap];omega
    have m:=mono 1 0 (by omega) (by omega)
    simp only [Nat.pow_one,Nat.zero_mul,Nat.pow_zero,Nat.mul_one] at m
    exact ht.trans (Nat.mul_le_mul_left _ (d.trans m))
  have ff : f≤256*L:=by
    apply resources.2.2.trans
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 256 (mono 3 75 (by omega) (by omega))
  refine ⟨t,z+(h+f),Encoding.capacity x.n a.gates,.seq run (.seq head out),?_,?_,fields.1,fields.2.1,?_,fields.2.2⟩
  · change z+(h+f) ≤ (c+Header.overhead+256)*x.cap^(D+4)*x.n^((b+75)*E)
    rw [Nat.mul_assoc,Nat.add_mul,Nat.add_mul]
    change z+(h+f) ≤ c*L+Header.overhead*L+256*L
    omega
  · change Encoding.capacity x.n a.gates ≤ (c+Header.overhead+256)*x.cap^(D+4)*x.n^((b+75)*E)
    rw [Nat.mul_assoc]
    apply resources.2.1.trans
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul (by omega) (mono 4 75 (by omega) (by omega))
  · change 1+5*(1+3*a.gates.size*x.n*x.n)<2+5*(1+3*a.gates.size*x.n*x.n)
    omega

end StableMSR.Recovery.CanonicalWriter

namespace StableMSR.Recovery.CanonicalWriter.Relative
open OracleQueries Compiler SingleCircuit SingleCodes SingleRAM WindowCSP
open WindowProfiles (keys piece)
open scoped Classical
set_option autoImplicit false

/-- A slot carries its local gates and a signed root token. The absent and stopped tokens are -1 and -2. -/
abbrev Packet := StableMSR.Recovery.NativeWriter.Relative.Packet
noncomputable def packet (x : World) (h w r : ℕ) : Packet :=
  if r%x.n ∈ keys x (r/x.n) then
    if 0 < scale x (r/x.n) then
      let c:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.region x (piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) h w
      ⟨c.1,(c.2:ℤ)⟩
    else ⟨#[],-2⟩
  else ⟨#[],-1⟩
/-- The next output position in a sequential concatenation of local gate lists. -/
noncomputable def firstGate (x : World) (h w : ℕ) : ℕ → ℕ
  | 0=>2 | r+1=>firstGate x h w r+(packet x h w r).gates.size
noncomputable def total (x : World) (h w : ℕ) :=
  max (firstGate x h w (x.rows*x.n)) ((x.rows*x.n+2)/3)

def displacement (op : Gate) (j v : ℕ) : ℤ :=
  if 1≤opCode op then (v:ℤ)-(j:ℤ) else (v:ℤ)

/-- Each predecessor is a displacement from the local gate's own ordinal. -/
def Record (n : ℕ) (s : Store) (p j : ℕ) (op : Gate) : Prop :=
  s.imem (word 1 p)=opCode op ∧
  s.imem (word 2 p)=displacement op j (leftID op) ∧
  s.imem (word 3 p)=displacement op j (rightID op) ∧
  ∀ i<n, s.imem (word 5 (p*n+i))=(if (tinyMask op).contains i then 1 else 0)

/-- The stream consists of the two initial records, successive local gate lists,
stop padding, and a directory of pairs (local root token, gate count). -/
def Reports (x : World) (h w : ℕ) (s : Store) : Prop :=
  let R:=x.rows*x.n
  let G:=total x h w
  s.ptrs 0=(x.n:ℤ) ∧ s.ptrs 1=(x.k:ℤ) ∧
  s.imem (word 0 0)=(G:ℤ) ∧ s.imem (word 0 1)=(x.rows:ℤ) ∧
  Record x.n s 0 0 (.atom []) ∧ Record x.n s 1 1 .stop ∧
  (∀ r<R, let c:=packet x h w r
    ∀ j<c.gates.size, Record x.n s (firstGate x h w r+j) j (gateAt c.gates j)) ∧
  (∀ p, firstGate x h w R≤p → p<G → Record x.n s p 0 .stop) ∧
  ∀ r<3*G,
    s.imem (word 4 r)=(if r<R then (packet x h w r).token else -1) ∧
    s.imem (word 6 r)=(if r<R then ((packet x h w r).gates.size:ℤ) else 0)

def GeneratesReports (e : ℚ) (c D b : ℕ) (cmd : Cmd) : Prop :=
  ∀ (x : World) (s : Store), 1 ≤ x.k → x.k < x.n → IsMetricArray x.dist → Ready x s →
    ∃ t z, Executes x.dist cmd s t z ∧ z ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      Reports x (budget (e:ℝ)) (widthBound (e:ℝ)) t
end StableMSR.Recovery.CanonicalWriter.Relative

namespace StableMSR.Recovery.CanonicalWriter.Relative
open OracleQueries Compiler SingleCircuit SingleCodes SingleRAM WindowCSP
open WindowProfiles (keys piece)
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000

def resolve (base token : ℤ) : ℤ := if 0≤token then base+token else -1-token
def adjust (tag : ℤ) (p : ℕ) (a : ℤ) := if 1≤tag then a+(p:ℤ) else a

theorem raw_succ (x : World) (h w r : ℕ) :
    StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w (r+1)=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.appendRegion x h w r (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w r) := by
  simp [StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly,List.range_succ]

theorem append_fields (x : World) (h w r : ℕ) (a : Assembly) :
    (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.appendRegion x h w r a).gates = a.gates ++ (packet x h w r).gates.map (relocateGate a.gates.size) ∧
    ((StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.appendRegion x h w r a).roots r:ℤ)=resolve a.gates.size (packet x h w r).token ∧
    ∀ i, i≠r → (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.appendRegion x h w r a).roots i=a.roots i := by
  by_cases key:r%x.n∈keys x (r/x.n)
  · by_cases pos:0<scale x (r/x.n)
    · simp [StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.appendRegion,packet,key,pos,resolve,Function.update_of_ne] <;> exact fun i hi=>Function.update_of_ne hi ..
    · simp [StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.appendRegion,packet,key,pos,resolve,Function.update_of_ne] <;> exact fun i hi=>Function.update_of_ne hi ..
  · simp [StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.appendRegion,packet,key,resolve,Function.update_of_ne] <;> exact fun i hi=>Function.update_of_ne hi ..

theorem raw_size (x : World) (h w r : ℕ) : (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w r).gates.size=firstGate x h w r := by
  induction r with
  | zero=>rfl
  | succ r ih=>rw [raw_succ,(append_fields ..).1,Array.size_append,Array.size_map,ih,firstGate]

theorem total_size (x : World) (h w : ℕ) : (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x h w).gates.size=total x h w := by
  unfold StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly padAssembly total
  simp only [Array.size_append,Array.size_replicate,raw_size]; omega

theorem raw_roots (x : World) (h w R r : ℕ) :
    ((StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w R).roots r:ℤ)=
      if r<R then resolve (firstGate x h w r) (packet x h w r).token else 0 := by
  induction R with
  | zero=>simp [StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly,emptyAssembly]
  | succ R ih=>
    rw [raw_succ]
    by_cases e:r=R
    · subst r;rw [(append_fields ..).2.1,raw_size,if_pos (by omega)]
    · rw [(append_fields ..).2.2 _ e,ih]
      by_cases q:r<R <;> simp [q,show (r<R+1)↔r<R by omega]

def Matches (n : ℕ) (s : Store) (p : ℕ) (op : Gate) : Prop :=
  s.imem (word 1 p)=opCode op ∧
  adjust (s.imem (word 1 p)) p (s.imem (word 2 p))=(leftID op:ℤ) ∧
  adjust (s.imem (word 1 p)) p (s.imem (word 3 p))=(rightID op:ℤ) ∧
  ∀ i<n, s.imem (word 5 (p*n+i))=(if (tinyMask op).contains i then 1 else 0)

theorem record_relocates (n : ℕ) (s : Store) (off j : ℕ) (op : Gate)
    (h : Record n s (off+j) j op) : Matches n s (off+j) (relocateGate off op) := by
  obtain ⟨tag,l,r,bit⟩:=h
  cases op <;> refine ⟨tag,?_,?_,bit⟩ <;>
    simp [relocateGate,tag,l,r,opCode,displacement,adjust,leftID,rightID] <;> omega

theorem record_stop (n : ℕ) (s : Store) (p j : ℕ) (h : Record n s p j .stop) : Matches n s p .stop := by
  obtain ⟨t,l,r,b⟩:=h
  exact ⟨t,by simp [adjust,t,opCode,l,displacement],by simp [adjust,t,opCode,r,displacement],b⟩

theorem raw_matches (x : World) (h w R : ℕ) (s : Store) (a0 : Record x.n s 0 0 (.atom []))
    (a1 : Record x.n s 1 1 .stop)
    (localData : ∀ r<R, let c:=packet x h w r
       ∀ j<c.gates.size, Record x.n s (firstGate x h w r+j) j (gateAt c.gates j)) :
    ∀p<(StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w R).gates.size, Matches x.n s p (gateAt (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w R).gates p) := by
  induction R with
  | zero=>
    intro p hp;change p<2 at hp
    interval_cases p
    · exact record_relocates x.n s 0 0 (.atom []) a0
    · exact record_stop x.n s 1 1 a1
  | succ R ih=>
    rw [raw_succ,(append_fields ..).1]
    let a:=(StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w R).gates
    let c:=(packet x h w R).gates
    change ∀p<(a++c.map (relocateGate a.size)).size,Matches x.n s p (gateAt (a++c.map (relocateGate a.size)) p)
    intro p hp
    by_cases old:p<a.size
    · simp only [gateAt,Array.getElem?_append_left old]
      exact ih (fun r hr=>localData r (by omega)) p old
    · let j:=p-a.size
      have eq:p=a.size+j:=by dsimp [j];omega
      have hj:j<c.size:=by simp only [Array.size_append,Array.size_map] at hp;dsimp [j];omega
      rw [eq]
      have rd:=localData R (by omega) j hj
      rw [←raw_size] at rd
      have good:=record_relocates x.n s a.size j (gateAt c j) rd
      have id : gateAt (a++c.map (relocateGate a.size)) (a.size+j)=relocateGate a.size (gateAt c j) := by
        simp only [gateAt,Array.getElem?_append_right (show a.size≤a.size+j by omega),
          Nat.add_sub_cancel_left,Array.getElem?_map]
        simp [getElem?_pos c j hj]
      rwa [id]

theorem reports_fields (x : World) (h w : ℕ) (s : Store) (rep : Reports x h w s) :
    let a:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x h w
    let R:=x.rows*x.n
    let carry:=fun r=>((firstGate x h w (min r R)):ℤ)
    a.gates.size=total x h w ∧ (∀p<a.gates.size,Matches x.n s p (gateAt a.gates p)) ∧
    ∀r<3*a.gates.size,
      carry r+s.imem (word 6 r)=carry (r+1) ∧
      resolve (carry r) (s.imem (word 4 r))=(a.roots r:ℤ) := by
  dsimp only
  obtain ⟨_,_,_,_,a0,a1,records,padding,directory⟩:=rep
  let R:=x.rows*x.n
  let raw:=(StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w R).gates
  refine ⟨total_size ..,?_,?_⟩
  · intro p hp
    by_cases hp0:p<raw.size
    · have h0:=raw_matches x h w R s a0 a1 records p hp0
      change Matches x.n s p (gateAt (raw++_) p)
      simpa only [gateAt,Array.getElem?_append_left hp0] using h0
    · have after : firstGate x h w R≤p:=by rw [←raw_size];exact Nat.le_of_not_gt hp0
      rw [total_size] at hp
      have stop:=record_stop _ _ _ _ (padding p after hp)
      change Matches x.n s p (gateAt (raw++Array.replicate _ .stop) p)
      simp only [gateAt,Array.getElem?_append_right (Nat.le_of_not_gt hp0),Array.getElem?_replicate]
      split <;> exact stop
  · intro r hr
    rw [total_size] at hr
    obtain ⟨rt,ln⟩:=directory r hr
    change _ ∧ _=((StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.rawAssembly x h w R).roots r:ℤ)
    rw [raw_roots,rt,ln]
    by_cases lo:r<R
    · have a:min r R=r:=Nat.min_eq_left (by omega)
      have b:min (r+1) R=r+1:=Nat.min_eq_left (by omega)
      change ((firstGate x h w (min r R):ℕ):ℤ)+_=_ ∧ resolve (firstGate x h w (min r R)) _=_
      simp [R] at lo a b ⊢
      simp [lo,a,b,firstGate]
    · have a:min r R=R:=Nat.min_eq_right (by omega)
      have b:min (r+1) R=R:=Nat.min_eq_right (by omega)
      change ((firstGate x h w (min r R):ℕ):ℤ)+_=_ ∧ resolve (firstGate x h w (min r R)) _=_
      change ¬r<x.rows*x.n at lo
      simp only [if_neg lo]
      simp [a,b,resolve,R,lo]

end StableMSR.Recovery.CanonicalWriter.Relative

namespace StableMSR.Recovery.CanonicalWriter.Relative.Machine
open Compiler
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 14000
def line : List Op → Cmd | []=>.skip | o::os=>.seq (.atom o) (line os)
noncomputable def perform {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) : List Op → Store
  | []=>s | o::os=>perform d (o.eval d s) os
theorem line_exec {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (os : List Op) :
    Executes d (line os) s (perform d s os) os.length := by
  induction os generalizing s with
  | nil=>exact .skip _
  | cons o os ih=>simpa only [line,perform,List.length_cons,Nat.add_comm 1] using Executes.seq (.atom o s) (ih (o.eval d s))

theorem word_inj {j f a b : ℕ} (hj : j<8) (hf : f<8) : word j a=word f b ↔ j=f ∧ a=b := by
  unfold word;omega

def edgesOps : List Op :=
  [.integerLoad 14 7,.pointerAdd 14 14 3,.integerStore 7 14,
   .integerLoad 14 8,.pointerAdd 14 14 3,.integerStore 8 14]
def edges := Cmd.seq (.atom (.integerLoad 14 6)) (.ite (.pointerLE 12 14) (line edgesOps) .skip)

structure Cursor (s : Store) (i m : ℕ) (base : ℤ) : Prop where
  idx : s.ptrs 3=(i:ℤ)
  remaining : s.ptrs 4=(m:ℤ)
  carry : s.ptrs 5=base
  tag : s.ptrs 6=word 1 i
  left : s.ptrs 7=word 2 i
  right : s.ptrs 8=word 3 i
  root : s.ptrs 9=word 4 i
  len : s.ptrs 10=word 6 i
  stride : s.ptrs 11=8
  one : s.ptrs 12=1
  zero : s.ptrs 13=0

theorem edges_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (i m : ℕ) (b : ℤ) (h : Cursor s i m b) :
    ∃ t z, Executes d edges s t z ∧ z≤8 ∧ (∀r<14, t.ptrs r=s.ptrs r) ∧
      ∀p, t.imem p=if p=word 2 i then adjust (s.imem (word 1 i)) i (s.imem p)
        else if p=word 3 i then adjust (s.imem (word 1 i)) i (s.imem p) else s.imem p := by
  let load:=Op.integerLoad 14 6
  let u:=load.eval d s
  have test : (Cond.pointerLE 12 14).test u ↔ (1 ≤ s.imem (word 1 i)) := by
    simp [u,load,Op.eval,Cond.test,h.one,h.tag]
  by_cases yes:1≤ s.imem (word 1 i)
  · let t:=perform d u edgesOps
    refine ⟨t,1+(1+edgesOps.length),.seq (.atom load s) (.ite_true (test.2 yes) (line_exec d u _)),by decide,?_,?_⟩
    · intro r hr
      simp [t,u,load,edgesOps,perform,Op.eval,Function.update_of_ne (by omega:r≠14)]
    · intro p
      have ne:word 3 i≠word 2 i:=by unfold word;omega
      by_cases e:p=word 2 i
      · subst p
        simp [t,u,load,perform,edgesOps,Op.eval,h.left,h.right,h.idx,ne,Ne.symm ne,adjust,yes]
      · by_cases f:p=word 3 i
        · subst p
          simp [t,u,load,perform,edgesOps,Op.eval,h.left,h.right,h.idx,ne,adjust,yes]
        · simp [t,u,load,perform,edgesOps,Op.eval,h.left,h.right,h.idx,ne,Function.update_of_ne e,
            Function.update_of_ne f,e,f]
  · refine ⟨u,1+(1+0+1),.seq (.atom load s) (.ite_false (fun e=>yes (test.1 e)) (.skip _)),by decide,?_,?_⟩
    · intro r hr;simp [u,load,Op.eval,Function.update_of_ne (by omega:r≠14)]
    · intro p;simp [u,load,Op.eval,adjust,yes]

theorem Cursor.transport {s t : Store} {i m : ℕ} {b : ℤ} (h : Cursor s i m b)
    (eq : ∀r<14, t.ptrs r=s.ptrs r) : Cursor t i m b := by
  constructor <;> first
    | exact (eq _ (by decide)).trans h.idx
    | exact (eq _ (by decide)).trans h.remaining
    | exact (eq _ (by decide)).trans h.carry
    | exact (eq _ (by decide)).trans h.tag
    | exact (eq _ (by decide)).trans h.left
    | exact (eq _ (by decide)).trans h.right
    | exact (eq _ (by decide)).trans h.root
    | exact (eq _ (by decide)).trans h.len
    | exact (eq _ (by decide)).trans h.stride
    | exact (eq _ (by decide)).trans h.one
    | exact (eq _ (by decide)).trans h.zero

def negative : List Op := [.pointerSub 14 13 14,.pointerDec 14]
def decodeRoot := Cmd.seq (.atom (.integerLoad 14 9)) (.ite (.pointerLE 13 14) (.atom (.pointerAdd 14 14 5)) (line negative))
theorem decode_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (i m : ℕ) (b : ℤ) (h : Cursor s i m b) :
    ∃ t z, Executes d decodeRoot s t z ∧ z≤5 ∧ (∀r<14, t.ptrs r=s.ptrs r) ∧
      t.imem=s.imem ∧ t.ptrs 14=resolve b (s.imem (word 4 i)) := by
  let o:=Op.integerLoad 14 9
  let u:=o.eval d s
  have test : (Cond.pointerLE 13 14).test u ↔ (0 ≤ s.imem (word 4 i)) := by simp [u,o,Op.eval,Cond.test,h.zero,h.root]
  by_cases pos:0≤ s.imem (word 4 i)
  · let f:=Op.pointerAdd 14 14 5
    refine ⟨f.eval d u,1+(1+1),.seq (.atom o s) (.ite_true (test.2 pos) (.atom f u)),by decide,?_,rfl,?_⟩
    · intro r hr;simp [f,u,o,Op.eval,Function.update_of_ne (by omega:r≠14)]
    · simp [f,u,o,Op.eval,h.root,h.carry,resolve,pos,add_comm]
  · refine ⟨perform d u negative,1+(1+negative.length+1),.seq (.atom o s)
      (.ite_false (fun e=>pos (test.1 e)) (line_exec d u _)),by decide,?_,rfl,?_⟩
    · intro r hr;simp [u,o,negative,perform,Op.eval,Function.update_of_ne (by omega:r≠14)]
    · simp [u,o,negative,perform,Op.eval,h.zero,h.root,resolve,pos];omega

def finish : List Op := [.integerStore 9 14,.integerLoad 14 10,.pointerAdd 5 5 14,
  .pointerInc 3,.pointerDec 4,.pointerSub 6 6 11,.pointerSub 7 7 11,.pointerSub 8 8 11,
  .pointerSub 9 9 11,.pointerSub 10 10 11]
def step : Cmd := .seq edges (.seq decodeRoot (line finish))

theorem finish_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (i m : ℕ) (b : ℤ)
    (h : Cursor s i (m+1) b) :
    let t:=perform d s finish
    Cursor t (i+1) m (b+s.imem (word 6 i)) ∧ (∀r<3,t.ptrs r=s.ptrs r) ∧
      ∀p, t.imem p=if p=word 4 i then s.ptrs 14 else s.imem p := by
  have ne:word 6 i≠word 4 i:=by unfold word;omega
  dsimp only
  refine ⟨?_,?_,?_⟩
  · constructor <;> simp [perform,finish,Op.eval,h.idx,h.remaining,h.carry,h.tag,h.left,h.right,h.root,h.len,h.stride,h.one,h.zero,ne,word] <;> ring
  · intro r hr;interval_cases r <;> simp [perform,finish,Op.eval]
  · intro p;simp [perform,finish,Op.eval,h.root,Function.update_apply]

end StableMSR.Recovery.CanonicalWriter.Relative.Machine

namespace StableMSR.Recovery.CanonicalWriter.Relative.Machine
open Compiler
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 14000

def corrected (s : Store) (carry : ℕ→ℤ) (j p : ℕ) : ℤ :=
  if j=2 ∨ j=3 then adjust (s.imem (word 1 p)) p (s.imem (word j p))
  else if j=4 then resolve (carry p) (s.imem (word 4 p)) else s.imem (word j p)
def View (s t : Store) (carry : ℕ→ℤ) (i : ℕ) :=
  ∀ j<8,∀p,t.imem (word j p) = if p < i then corrected s carry j p else s.imem (word j p)

theorem step_run {n : ℕ} (d : Point n→Point n→ℝ) (s t : Store) (i m : ℕ) (carry : ℕ→ℤ)
    (c : Cursor t i (m+1) (carry i)) (v : View s t carry i)
    (next : carry i+s.imem (word 6 i)=carry (i+1)) :
    ∃ u z, Executes d step t u z ∧ z≤23 ∧ Cursor u (i+1) m (carry (i+1)) ∧
      (∀r<3,u.ptrs r=t.ptrs r) ∧ View s u carry (i+1) := by
  obtain ⟨a,z,ea,ta,ka,ma⟩:=edges_run d t i (m+1) _ c
  have ca:=c.transport ka
  obtain ⟨b,f,eb,tb,kb,mb,rb⟩:=decode_run d a i (m+1) _ ca
  have cb:=ca.transport kb
  let u:=perform d b finish
  obtain ⟨cu,keep,mu⟩:=finish_run d b i m _ cb
  have old (j : ℕ) (hj : j<8) : t.imem (word j i)=s.imem (word j i) := by simpa using v j hj i
  have fresh (j : ℕ) (hj : j<8) (j2 : j≠2) (j3 : j≠3) : a.imem (word j i)=s.imem (word j i) := by
    rw [ma];simp [word_inj hj (by decide : 2<8),word_inj hj (by decide : 3<8),j2,j3,old j hj]
  have len := fresh 6 (by decide) (by decide) (by decide)
  have tok := fresh 4 (by decide) (by decide) (by decide)
  rw [mb,len,next] at cu
  refine ⟨u,z+(f+finish.length),.seq ea (.seq eb (line_exec d b _)),?_,cu,?_,?_⟩
  · change z+(f+10)≤23;omega
  · intro r hr;exact (keep r hr).trans ((kb r (by omega)).trans (ka r (by omega)))
  · intro j hj p
    rw [mu,rb,tok,mb,ma]
    by_cases eq:p=i
    · subst p
      simp only [Nat.lt_succ_self,if_true,word_inj hj (by decide : 4<8),word_inj hj (by decide : 2<8),
        word_inj hj (by decide : 3<8),and_true,old 1 (by decide),old j hj]
      by_cases j4:j=4 <;> by_cases j2:j=2 <;> by_cases j3:j=3 <;> simp_all [corrected]
    · have a4:word j p≠word 4 i:=by rw [ne_eq,word_inj hj (by decide)];simp [eq]
      have a2:word j p≠word 2 i:=by rw [ne_eq,word_inj hj (by decide)];simp [eq]
      have a3:word j p≠word 3 i:=by rw [ne_eq,word_inj hj (by decide)];simp [eq]
      simpa only [if_neg a4,if_neg a2,if_neg a3,show (p < i+1)↔p < i by omega] using v j hj p

def control : Cmd := .whileDo (.pointerLE 12 4) step

theorem loop_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (L : ℕ) (carry : ℕ→ℤ)
    (inc : ∀i<L, carry i+s.imem (word 6 i)=carry (i+1)) (m i : ℕ) (bound : i+m=L) (t : Store)
    (c : Cursor t i m (carry i)) (v : View s t carry i) :
    ∃u z,Executes d control t u z ∧ z≤2+25*m ∧ (∀r<3,u.ptrs r=t.ptrs r) ∧ View s u carry L := by
  induction m generalizing i t with
  | zero =>
    have il:i=L:=by omega
    refine ⟨t,2,Executes.while_false ?_,by omega,fun _ _=>rfl,by simpa [←il] using v⟩
    change ¬t.ptrs 12≤t.ptrs 4;rw [c.one,c.remaining];decide
  | succ m ih =>
    obtain ⟨u,z,go,cost,cu,ku,vu⟩:=step_run d s t i m carry c v (inc i (by omega))
    obtain ⟨w,l,loop,rest,kw,vw⟩:=ih (i+1) (by omega) u cu vu
    have yes:(Cond.pointerLE 12 4).test t:=by change t.ptrs 12≤t.ptrs 4;rw [c.one,c.remaining];omega
    refine ⟨w,1+z+1+l,Executes.while_true yes go loop,by omega,fun r hr=>(kw r hr).trans (ku r hr),vw⟩

def startOps : List Op := [
  .pointerConst 14 (word 0 0),.integerLoad 4 14,.pointerCopy 14 4,.pointerAdd 4 4 4,.pointerAdd 4 4 14,
  .pointerConst 3 0,.pointerConst 5 2,.pointerConst 6 (word 1 0),.pointerConst 7 (word 2 0),
  .pointerConst 8 (word 3 0),.pointerConst 9 (word 4 0),.pointerConst 10 (word 6 0),
  .pointerConst 11 8,.pointerConst 12 1,.pointerConst 13 0]
def relocate : Cmd := .seq (line startOps) control

theorem relocate_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (G : ℕ) (carry : ℕ→ℤ)
    (cnt : s.imem (word 0 0)=(G:ℤ)) (start : carry 0=2)
    (inc : ∀i<3*G, carry i+s.imem (word 6 i)=carry (i+1)) :
    ∃t z, Executes d relocate s t z ∧ z≤17+75*G ∧ (∀r<3,t.ptrs r=s.ptrs r) ∧ View s t carry (3*G) := by
  let u:=perform d s startOps
  have c : Cursor u 0 (3*G) (carry 0) := by
    constructor <;> simp [u,perform,startOps,Op.eval,cnt,start] <;> ring
  have v : View s u carry 0 := by intro j hj p;simp [u,perform,startOps,Op.eval]
  obtain ⟨t,z,go,cost,keep,out⟩:=loop_run d s (3*G) carry inc (3*G) 0 (by omega) u c v
  refine ⟨t,startOps.length+z,.seq (line_exec d s _) go,?_,?_,out⟩
  · change 15+z≤17+75*G;omega
  · intro r hr;rw [keep _ hr];interval_cases r <;> simp [u,perform,startOps,Op.eval]

end StableMSR.Recovery.CanonicalWriter.Relative.Machine

namespace StableMSR.Recovery.CanonicalWriter.Relative
open Compiler OracleQueries SingleCircuit SingleRAM
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem native_relative_relocation_pass :
    ∃ cmd : Cmd, ∀ (x : World) (h w : ℕ) (s : Store), Reports x h w s →
      ∃ t z, Executes x.dist cmd s t z ∧ z ≤ 17+75*total x h w ∧
        let a := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x h w
        Columns x.n x.k x.rows a.gates a.roots t := by
  refine ⟨Machine.relocate,?_⟩
  intro x h w s rep
  let a:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x h w
  let carry:=fun r=>((firstGate x h w (min r (x.rows*x.n))):ℤ)
  obtain ⟨sz,all,dir⟩:=reports_fields x h w s rep
  obtain ⟨sn,sk,cnt,rows,_⟩:=rep
  obtain ⟨t,z,run,cost,keep,view⟩:=Machine.relocate_run x.dist s a.gates.size carry
    (by simpa only [a,sz] using cnt) (by simp [carry,firstGate]) (fun i hi=>(dir i hi).1)
  have same (j : ℕ) (hj : j<8) (j2 : j≠2) (j3 : j≠3) (j4 : j≠4) (p : ℕ) :
      t.imem (word j p)=s.imem (word j p) := by
    simpa [Machine.corrected,j2,j3,j4] using view j hj p
  refine ⟨t,z,run,by simpa only [a,sz] using cost,(keep 0 (by decide)).trans sn,(keep 1 (by decide)).trans sk,
    (same 0 (by decide) (by decide) (by decide) (by decide) 0).trans (by simpa only [a,sz] using cnt),
    (same 0 (by decide) (by decide) (by decide) (by decide) 1).trans rows,?_,?_,?_⟩
  · intro p hp
    obtain ⟨tag,l,r,_⟩:=all p hp
    have h3:p<3*a.gates.size:=by change p<a.gates.size at hp;omega
    refine ⟨(same 1 (by decide) (by decide) (by decide) (by decide) p).trans tag,?_,?_⟩
    · simpa [view 2 (by decide) p,h3,Machine.corrected] using l
    · simpa [view 3 (by decide) p,h3,Machine.corrected] using r
  · intro r hr
    have ir:=view 4 (by decide) r
    have h3:r<3*a.gates.size:=hr
    simp only [h3,if_true,Machine.corrected,show ¬(4=2 ∨ 4=3) by decide,if_false] at ir
    exact ir.trans (dir r hr).2
  · intro p hp i hi
    exact (same 5 (by decide) (by decide) (by decide) (by decide) _).trans ((all p hp).2.2.2 i hi)

end StableMSR.Recovery.CanonicalWriter.Relative

namespace StableMSR.Recovery.CanonicalWriter.Relative
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP
set_option autoImplicit false

theorem columns_of_reports
    (resources : ∀ (x : World) (e : ℚ), 0<e → e<1 → 2≤x.n →
      let G:=(StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x (budget (e:ℝ)) (widthBound (e:ℝ))).gates.size
      82+42*G+7*(G*x.n)≤256*x.cap^3*x.n^(75*parameterEnvelope (e:ℝ)))
    (pass : ∃cmd : Cmd, ∀(x : World) (h w : ℕ) (s : Store), Reports x h w s →
      ∃t z, Executes x.dist cmd s t z ∧ z≤17+75*total x h w ∧
        let a:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x h w
        Columns x.n x.k x.rows a.gates a.roots t)
    (source : ∃c D b : ℕ, ∀e : ℚ, 0<e → e<1 → ∃cmd : Cmd, GeneratesReports e c D b cmd) :
    ∃c D b : ℕ, ∀e : ℚ, 0<e → e<1 → ∃cmd : Cmd, GeneratesColumns e c D b cmd := by
  obtain ⟨c,D,b,gen⟩:=source
  obtain ⟨rel,correct⟩:=pass
  refine ⟨c+512,D+3,b+75,?_⟩
  intro e he hl
  obtain ⟨src,make⟩:=gen e he hl
  refine ⟨.seq src rel,?_⟩
  intro x s hk kn met ready
  obtain ⟨u,z,go,work,raw⟩:=make x s hk kn met ready
  obtain ⟨v,f,run,tm,done⟩:=correct x (budget (e:ℝ)) (widthBound (e:ℝ)) u raw
  let E:=parameterEnvelope (e:ℝ)
  let A:=x.n^(75*E)
  let G:=(StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly x (budget (e:ℝ)) (widthBound (e:ℝ))).gates.size
  have lim : 82+42*G+7*(G*x.n)≤256*(x.cap^3*A) := by
    simpa only [Nat.mul_assoc] using resources x e he hl (by omega)
  have small : f≤17+75*G := by rwa [← total_size] at tm
  have ft : f≤512*(x.cap^3*A) := by omega
  let L:=x.cap^(D+3)*x.n^((b+75)*E)
  have cp:1≤x.cap:=by dsimp [World.cap];omega
  have lift (d t : ℕ) (hd : d≤D+3) (ht : t≤b+75) : x.cap^d*x.n^(t*E) ≤ L :=
    Nat.mul_le_mul (Nat.pow_le_pow_right cp hd) (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ ht))
  have z0 : z≤c*L:=work.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c (lift D b (by omega) (by omega)))
  have f0 : f≤512*L:=ft.trans (Nat.mul_le_mul_left 512 (lift 3 75 (by omega) (by omega)))
  refine ⟨v,z+f,.seq go run,?_,done⟩
  change z+f≤(c+512)*x.cap^(D+3)*x.n^((b+75)*E)
  rw [Nat.mul_assoc,Nat.add_mul]
  exact Nat.add_le_add z0 f0

end StableMSR.Recovery.CanonicalWriter.Relative

namespace StableMSR.Recovery.CanonicalWriter.Relative
open OracleQueries Compiler SingleCircuit WindowCSP
set_option autoImplicit false

/-- The four calls made by the global controller. Only a regional call inspects the scene. -/
abbrev Request := StableMSR.Recovery.NativeWriter.Relative.Request
noncomputable def payload (x : World) (h w r : ℕ) : Request → Gates
  | .seed=>#[.atom [],.stop] | .region=>(packet x h w r).gates | .pad=>#[.stop] | .absent=>#[]
noncomputable def directory (x : World) (h w r : ℕ) : Request → Option (ℤ×ℕ)
  | .region=>some ((packet x h w r).token,(packet x h w r).gates.size)
  | .absent=>some (-1,0) | _=>none
def DirAt (s : Store) (r : ℕ) (v : ℤ×ℕ) := s.imem (word 4 r)=v.1 ∧ s.imem (word 6 r)=(v.2:ℤ)

/-- A single packet call reads (slot, gate cursor) from registers 3 and 4.
It returns the length in register 7, preserves the original scene and earlier records,
and writes just the packet and its directory entry when present. -/
def PacketCall (x : World) (h w r p : ℕ) (q : Request) (s t : Store) : Prop :=
  let g:=payload x h w r q
  Ready x t ∧ (∀ i ∈ [3,4,5], t.ptrs i=s.ptrs i) ∧ t.ptrs 7=(g.size:ℤ) ∧
  (∀j<g.size, Record x.n t (p+j) j (gateAt g j)) ∧
  (∀v, directory x h w r q=some v → DirAt t r v) ∧
  (∀a<p,∀j op,Record x.n s a j op → Record x.n t a j op) ∧
  ∀a<r,∀v,DirAt s a v → DirAt t a v

def PacketGenerator (e : ℚ) (c D b : ℕ) (call : Request→Cmd) : Prop :=
  ∀(x : World) (s : Store), 1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀(q : Request) (r p : ℕ), s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) →
    (q=StableMSR.Recovery.NativeWriter.Relative.Request.region → r<x.rows*x.n) →
    ∃t z, Executes x.dist (call q) s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      PacketCall x (budget (e:ℝ)) (widthBound (e:ℝ)) r p q s t

end StableMSR.Recovery.CanonicalWriter.Relative

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 14000

def count (q : Request) : ℕ := match q with | .region | .absent=>1 | _=>0
structure Head (x : World) (r p : ℕ) (s : Store) : Prop where
  ready : Ready x s
  slot : s.ptrs 3=(r:ℤ)
  gate : s.ptrs 4=(p:ℤ)
  slots : s.ptrs 5=(x.rows*x.n:ℕ)
structure At (x : World) (r p : ℕ) (s : Store) : Prop extends Head x r p s where
  nextRow : s.ptrs 6=(r+1:ℕ)
  triple : s.ptrs 8=(3*p:ℕ)
  nextTriple : s.ptrs 9=(3*p+1:ℕ)
structure Writes (x : World) (h w r p : ℕ) (q : Request) (s t : Store) : Prop where
  gates : ∀ j<(payload x h w r q).size, Record x.n t (p+j) j (gateAt (payload x h w r q) j)
  dir : ∀v,directory x h w r q=some v → DirAt t r v
  oldGate : ∀a<p,∀j op,Record x.n s a j op → Record x.n t a j op
  oldDir : ∀a<r,∀v,DirAt s a v → DirAt t a v

def afterOps (q : Request) : List Op :=
  (if count q=1 then [.pointerInc 3] else []) ++
  [.pointerAdd 4 4 7,.pointerCopy 6 3,.pointerInc 6,.pointerAdd 8 4 4,
   .pointerAdd 8 8 4,.pointerCopy 9 8,.pointerInc 9]
def emit (call : Request→Cmd) (q : Request) := Cmd.seq (call q) (line (afterOps q))
def Runs (x : World) (h w T : ℕ) (call : Request→Cmd) :=
  ∀q r p s, Head x r p s → (q=StableMSR.Recovery.NativeWriter.Relative.Request.region → r<x.rows*x.n) →
    ∃t z,Executes x.dist (call q) s t z ∧ z≤T ∧ PacketCall x h w r p q s t

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000
theorem emit_run (x : World) (h w T : ℕ) (call : Request→Cmd) (run : Runs x h w T call)
    (q : Request) (r p : ℕ) (s : Store) (hd : Head x r p s) (valid : q=StableMSR.Recovery.NativeWriter.Relative.Request.region → r<x.rows*x.n) :
    ∃t z,Executes x.dist (emit call q) s t z ∧ z≤T+8 ∧
      At x (r+count q) (p+(payload x h w r q).size) t ∧ Writes x h w r p q s t := by
  obtain ⟨u,z,go,cost,ready,regs,len,gate,dir,earlier,prev⟩:=run q r p s hd valid
  let t:=perform x.dist u (afterOps q)
  have r3 : u.ptrs 3=(r:ℤ):=(regs 3 (by simp)).trans hd.slot
  have r4 : u.ptrs 4=(p:ℤ):=(regs 4 (by simp)).trans hd.gate
  have r5 : u.ptrs 5=(x.rows*x.n:ℕ):=(regs 5 (by simp)).trans hd.slots
  have tm:(afterOps q).length≤8:=by cases q <;> decide
  have fl : t.imem=u.imem:=by cases q <;> rfl
  have low (i : ℕ) (hi : i<3) : t.ptrs i=u.ptrs i := by
    interval_cases i <;> cases q <;> simp [t,afterOps,count,perform,Op.eval]
  have rd : Ready x t := by
    constructor
    · intro ax
      have small:ax.reg<3:=by cases ax <;> decide
      exact (low ax.reg small).trans (ready.1 ax)
    · intro i;rw [fl,ready.2]
  refine ⟨t,z+(afterOps q).length,.seq go (line_exec x.dist u _),by omega,?_,?_⟩
  · refine ⟨⟨rd,?_,?_,?_⟩,?_,?_,?_⟩ <;> cases q <;>
      simp [t,afterOps,count,perform,Op.eval,r3,r4,r5,len] <;> ring
  · have rr (a j : ℕ) (op : Gate) : Record x.n t a j op ↔ Record x.n u a j op := by simp only [Record,fl]
    have dd (a : ℕ) (v : ℤ×ℕ) : DirAt t a v ↔ DirAt u a v := by simp only [DirAt,fl]
    exact ⟨fun j hj=>(rr ..).2 (gate j hj),fun v hv=>(dd ..).2 (dir v hv),
      fun a ha j op old=>(rr ..).2 (earlier a ha j op old),fun a ha v old=>(dd ..).2 (prev a ha v old)⟩

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000
theorem firstGate_mono (x : World) (h w : ℕ) : Monotone (firstGate x h w) :=
  monotone_nat_of_le_succ (fun r=>by rw [firstGate];omega)

noncomputable def wanted (x : World) (h w r : ℕ) : ℤ×ℕ :=
  if r<x.rows*x.n then ((packet x h w r).token,(packet x h w r).gates.size) else (-1,0)
structure Past (x : World) (h w m r p : ℕ) (s : Store) : Prop where
  seed0 : Record x.n s 0 0 (.atom [])
  seed1 : Record x.n s 1 1 .stop
  blocks : ∀ a < m, ∀j<(packet x h w a).gates.size,
    Record x.n s (firstGate x h w a+j) j (gateAt (packet x h w a).gates j)
  padding : ∀a,firstGate x h w m≤a → a<p → Record x.n s a 0 .stop
  dirs : ∀a<r, DirAt s a (wanted x h w a)

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000
theorem seed_past (x : World) (h w : ℕ) (s t : Store) (wr : Writes x h w 0 0 .seed s t) :
    Past x h w 0 0 2 t :=
  ⟨wr.gates 0 (by change 0<2;decide),wr.gates 1 (by change 1<2;decide),fun a e=>by omega,
   fun a ha ha2=>by change 2≤a at ha;omega,fun a ha=>by omega⟩

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000
theorem slot_past (x : World) (h w r : ℕ) (s t : Store) (hr : r<x.rows*x.n)
    (old : Past x h w r r (firstGate x h w r) s) (wr : Writes x h w r (firstGate x h w r) .region s t) :
    Past x h w (r+1) (r+1) (firstGate x h w (r+1)) t := by
  let F:=firstGate x h w
  have two : 2≤F r:=firstGate_mono x h w (Nat.zero_le r)
  refine ⟨wr.oldGate _ (by change 0<F r;omega) _ _ old.seed0,wr.oldGate _ (by change 1<F r;omega) _ _ old.seed1,?_,?_,?_⟩
  · intro a ha j hj
    by_cases e:a=r
    · subst a;exact wr.gates j hj
    · have before:=firstGate_mono x h w (show a+1≤r by omega)
      change F a+(packet x h w a).gates.size≤F r at before
      exact wr.oldGate _ (by change F a+j<F r;omega) _ _ (old.blocks a (by omega) j hj)
  · intro a ha hb;omega
  · intro a ha
    by_cases e:a=r
    · subst a
      simpa only [wanted,if_pos hr] using wr.dir _ rfl
    · exact wr.oldDir _ (by omega) _ (old.dirs _ (by omega))

theorem pad_past (x : World) (h w R p : ℕ) (s t : Store) (hp : firstGate x h w R≤p)
    (old : Past x h w R R p s) (wr : Writes x h w R p .pad s t) :
    Past x h w R R (p+1) t := by
  have two:2≤p:=(firstGate_mono x h w (Nat.zero_le R)).trans hp
  refine ⟨wr.oldGate _ (by omega) _ _ old.seed0,wr.oldGate _ (by omega) _ _ old.seed1,?_,?_,fun a ha=>wr.oldDir _ ha _ (old.dirs a ha)⟩
  · intro a ha j hj
    have before:=(firstGate_mono x h w (show a+1≤R by omega)).trans hp
    rw [firstGate] at before
    exact wr.oldGate _ (by omega) _ _ (old.blocks a ha j hj)
  · intro a ha hb
    by_cases e:a=p
    · subst a;exact wr.gates 0 (by change 0<1;decide)
    · exact wr.oldGate _ (by omega) _ _ (old.padding a ha (by omega))

theorem tail_past (x : World) (h w r p : ℕ) (s t : Store) (hr : x.rows*x.n≤r)
    (hp : firstGate x h w (x.rows*x.n)≤p) (old : Past x h w (x.rows*x.n) r p s)
    (wr : Writes x h w r p .absent s t) : Past x h w (x.rows*x.n) (r+1) p t := by
  have two:2≤p:=(firstGate_mono x h w (Nat.zero_le _)).trans hp
  refine ⟨wr.oldGate _ (by omega) _ _ old.seed0,wr.oldGate _ (by omega) _ _ old.seed1,?_,?_,?_⟩
  · intro a ha j hj
    have before:=(firstGate_mono x h w (show a+1≤x.rows*x.n by omega)).trans hp
    rw [firstGate] at before
    exact wr.oldGate _ (by omega) _ _ (old.blocks a ha j hj)
  · intro a ha hb;exact wr.oldGate _ hb _ _ (old.padding a ha hb)
  · intro a ha
    by_cases e:a=r
    · subst a;simpa [wanted,Nat.not_lt.mpr hr] using wr.dir _ rfl
    · exact wr.oldDir _ (by omega) _ (old.dirs a (by omega))

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler Machine
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Registers below b and all integer memory survive evaluation of a header expression. -/
def Frame (b : ℕ) (s t : Store) := (∀ i<b, t.ptrs i=s.ptrs i) ∧ t.imem=s.imem
theorem frame_trans {b : ℕ} {s t u : Store} (h : Frame b s t) (v : Frame b t u) : Frame b s u :=
  ⟨fun i hi => (v.1 i hi).trans (h.1 i hi),v.2.trans h.2⟩

def addBody (b : ℕ) : List Op := [.pointerAdd b b (b+1),.pointerDec (b+2)]
def addLoop (b : ℕ) : Cmd := .whileDo (.pointerLE (b+3) (b+2)) (line (addBody b))

theorem addLoop_run {n : ℕ} (d : Point n→Point n→ℝ) (b m : ℕ) (s : Store) (a v : ℤ)
    (ha : s.ptrs b=a) (hv : s.ptrs (b+1)=v) (hm : s.ptrs (b+2)=(m:ℤ)) (ho : s.ptrs (b+3)=1) :
    ∃ t, Executes d (addLoop b) s t (2+4*m) ∧ Frame b s t ∧ t.ptrs b=a+(m:ℤ)*v := by
  induction m generalizing s a with
  | zero =>
    refine ⟨s,Executes.while_false ?_,⟨fun _ _=>rfl,rfl⟩,by simpa using ha⟩
    change ¬ s.ptrs (b+3) ≤ s.ptrs (b+2)
    rw [ho,hm];decide
  | succ m ih =>
    let t:=perform d s (addBody b)
    have ht : Frame b s t := by
      refine ⟨?_,rfl⟩;intro i hi
      simp [t,perform,addBody,Op.eval,Function.update_of_ne (by omega : i≠b+2),Function.update_of_ne (by omega : i≠b)]
    obtain ⟨u,go,hu,final⟩:=ih t (a+v) (by simp [t,perform,addBody,Op.eval,ha,hv])
      (by simp [t,perform,addBody,Op.eval,hv]) (by simp [t,perform,addBody,Op.eval,hm])
      (by simp [t,perform,addBody,Op.eval,ho])
    have yes : (Cond.pointerLE (b+3) (b+2)).test s := by change s.ptrs _ ≤ s.ptrs _;rw [ho,hm];omega
    have all:=Executes.while_true yes (line_exec d s (addBody b)) go
    refine ⟨u,?_,frame_trans ht hu,?_⟩
    · simpa only [addLoop,show 1+(addBody b).length+1+(2+4*m)=2+4*(m+1) by change 1+2+1+_= _;omega] using all
    · rw [final];push_cast;ring

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 14000
def start : List Op := [.pointerConst 3 0,.pointerConst 4 0,.pointerConst 5 0,
  .pointerCopy 6 2,.pointerCopy 7 0,.pointerConst 8 1]
def beginProgram : Cmd := .seq (line start) (addLoop 5)
theorem begin_run (x : World) (s : Store) (rd : Ready x s) :
    ∃t, Executes x.dist beginProgram s t (8+4*x.n) ∧ Head x 0 0 t := by
  let u:=perform x.dist s start
  have pts:s.ptrs 0=(x.n:ℤ):=rd.1 .points
  have rows:s.ptrs 2=(x.rows:ℤ):=rd.1 .rows
  obtain ⟨t,go,fr,endval⟩:=addLoop_run x.dist 5 x.n u 0 (x.rows:ℤ)
    (by simp [u,perform,start,Op.eval]) (by simp [u,perform,start,Op.eval,rows])
    (by simp [u,perform,start,Op.eval,pts]) (by simp [u,perform,start,Op.eval])
  refine ⟨t,?_,⟨⟨?_,?_⟩,?_,?_,?_⟩⟩
  · have h:=Executes.seq (line_exec x.dist s start) go
    simpa only [beginProgram,show start.length+(2+4*x.n)=8+4*x.n by change 6+_= _;omega] using h
  · intro ax;cases ax <;> simpa [u,start,perform,Op.eval,Axis.reg,World.size] using
      (fr.1 _ (by decide)).trans (by first | exact rd.1 .points | exact rd.1 .blocks | exact rd.1 .rows)
  · intro i;rw [fr.2];exact rd.2 i
  · simpa [u,perform,start,Op.eval] using fr.1 3 (by decide)
  · simpa [u,perform,start,Op.eval] using fr.1 4 (by decide)
  · simpa [mul_comm] using endval

/-- A guarded loop over any prescribed finite list of consecutive states. -/
theorem bounded_loop (x : World) (c : Cond) (body : Cmd) (I : ℕ→Store→Prop) (N T : ℕ)
    (guard : ∀ i s, I i s → (c.test s ↔ i<N))
    (advance : ∀ i<N, ∀s, I i s → ∃t z,Executes x.dist body s t z ∧ z≤T ∧ I (i+1) t)
    (s : Store) (init : I 0 s) :
    ∃t z,Executes x.dist (.whileDo c body) s t z ∧ z≤2+N*(T+2) ∧ I N t := by
  have loop (m i : ℕ) (eq : i+m=N) (s : Store) (p : I i s) :
      ∃t z,Executes x.dist (.whileDo c body) s t z ∧ z≤2+m*(T+2) ∧ I N t := by
    induction m generalizing i s with
    | zero=>
      have same:i=N:=by omega
      exact ⟨s,2,.while_false (fun h=>by have:= (guard i s p).1 h;omega),by omega,by simpa [←same] using p⟩
    | succ m ih=>
      have span:i<N:=by omega
      obtain ⟨u,z,go,work,next⟩:=advance i span s p
      obtain ⟨t,f,nextgo,rest,out⟩:=ih (i+1) (by omega) u next
      refine ⟨t,1+z+1+f,.while_true ((guard i s p).2 span) go nextgo,?_,out⟩
      rw [Nat.succ_mul];omega
  exact loop N 0 (by omega) s init

def slotGuard := Cond.pointerLE 6 5
def padGuard := Cond.pointerLE 9 5
def tailGuard := Cond.pointerLE 6 8

theorem real_slots (x : World) (h w T : ℕ) (call : Request→Cmd) (run : Runs x h w T call) (s : Store)
    (a : At x 0 2 s) (hist : Past x h w 0 0 2 s) :
    let R:=x.rows*x.n
    ∃t z, Executes x.dist (.whileDo slotGuard (emit call .region)) s t z ∧ z≤2+R*(T+10) ∧
      At x R (firstGate x h w R) t ∧ Past x h w R R (firstGate x h w R) t := by
  let R:=x.rows*x.n
  let I:=fun r t=>At x r (firstGate x h w r) t ∧ Past x h w r r (firstGate x h w r) t
  apply bounded_loop x slotGuard (emit call .region) I R (T+8) ?_ ?_ s ⟨a,hist⟩
  · intro r t it
    change t.ptrs 6≤t.ptrs 5 ↔ (r<R)
    rw [it.1.nextRow,it.1.slots];dsimp [R];omega
  · intro r hr t it
    obtain ⟨u,z,go,work,out,wr⟩:=emit_run x h w T call run .region r (firstGate x h w r) t it.1.toHead (fun _=>hr)
    exact ⟨u,z,go,work,out,slot_past x h w r t u hr it.2 wr⟩

theorem padding_slots (x : World) (h w T : ℕ) (call : Request→Cmd) (run : Runs x h w T call) (s : Store)
    (a : At x (x.rows*x.n) (firstGate x h w (x.rows*x.n)) s)
    (hist : Past x h w (x.rows*x.n) (x.rows*x.n) (firstGate x h w (x.rows*x.n)) s) :
    let R:=x.rows*x.n
    let raw:=firstGate x h w R
    let G:=total x h w
    ∃t z, Executes x.dist (.whileDo padGuard (emit call .pad)) s t z ∧ z≤2+(G-raw)*(T+10) ∧
      At x R G t ∧ Past x h w R R G t := by
  let R:=x.rows*x.n
  let raw:=firstGate x h w R
  let G:=total x h w
  have le:raw≤G:=Nat.le_max_left .. 
  let I:=fun i t=>At x R (raw+i) t ∧ Past x h w R R (raw+i) t
  have go:=bounded_loop x padGuard (emit call .pad) I (G-raw) (T+8) (by
    intro i t it
    change t.ptrs 9≤t.ptrs 5 ↔ (i<G-raw)
    rw [it.1.nextTriple,it.1.slots]
    change ((3*(raw+i)+1:ℕ):ℤ)≤(R:ℤ) ↔ (i < max raw ((R+2)/3)-raw)
    omega) (by
    intro i hi t it
    obtain ⟨u,z,go,tm,out,wr⟩:=emit_run x h w T call run .pad R (raw+i) t it.1.toHead (by intro e;cases e)
    refine ⟨u,z,go,tm,?_,?_⟩
    · simpa only [count,Nat.add_zero,payload,show (#[(SingleCircuit.Gate.stop)]).size=1 by rfl,Nat.add_assoc] using out
    · simpa only [Nat.add_assoc] using pad_past x h w R (raw+i) t u (by change raw≤raw+i;omega) it.2 wr)
    s (by simpa only [I,Nat.add_zero] using And.intro a hist)
  simpa only [I,Nat.add_sub_of_le le,show raw+(G-raw)=G by omega] using go

theorem absent_slots (x : World) (h w T : ℕ) (call : Request→Cmd) (run : Runs x h w T call) (s : Store)
    (a : At x (x.rows*x.n) (total x h w) s)
    (hist : Past x h w (x.rows*x.n) (x.rows*x.n) (total x h w) s) :
    let R:=x.rows*x.n
    let G:=total x h w
    ∃t z,Executes x.dist (.whileDo tailGuard (emit call .absent)) s t z ∧ z≤2+(3*G-R)*(T+10) ∧
      At x (3*G) G t ∧ Past x h w R (3*G) G t := by
  let R:=x.rows*x.n
  let G:=total x h w
  have le:R≤3*G:=by dsimp [R,G,total];omega
  let I:=fun i t=>At x (R+i) G t ∧ Past x h w R (R+i) G t
  have go:=bounded_loop x tailGuard (emit call .absent) I (3*G-R) (T+8) (by
    intro i t it
    change t.ptrs 6≤t.ptrs 8 ↔ (i<3*G-R)
    rw [it.1.nextRow,it.1.triple];omega) (by
    intro i hi t it
    obtain ⟨u,z,go,tm,out,wr⟩:=emit_run x h w T call run .absent (R+i) G t it.1.toHead (by intro e;cases e)
    refine ⟨u,z,go,tm,?_,?_⟩
    · exact out
    · simpa only [Nat.add_assoc] using tail_past x h w (R+i) G t u (by change R≤R+i;omega) (Nat.le_max_left ..) it.2 wr)
    s (by simpa only [I,Nat.add_zero] using And.intro a hist)
  simpa only [I,show R+(3*G-R)=3*G by omega] using go

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP Machine
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 14000
def saveCounts : List Op := [.pointerConst 10 (word 0 0),.integerStore 10 4,.pointerConst 10 (word 0 1),.integerStore 10 2]

theorem finish_reports (x : World) (h w : ℕ) (s : Store) (hd : At x (3*total x h w) (total x h w) s)
    (past : Past x h w (x.rows*x.n) (3*total x h w) (total x h w) s) :
    Reports x h w (perform x.dist s saveCounts) := by
  let t:=perform x.dist s saveCounts
  have m (j i : ℕ) (hj : j<8) (nz : j≠0) : t.imem (word j i)=s.imem (word j i) := by
    simp [t,perform,saveCounts,Op.eval,Function.update_apply,word_inj hj (by decide : 0<8),nz]
  have retains (p j : ℕ) (a : Gate) (v : Record x.n s p j a) : Record x.n t p j a :=
    ⟨(m 1 _ (by decide) (by decide)).trans v.1,(m 2 _ (by decide) (by decide)).trans v.2.1,
      (m 3 _ (by decide) (by decide)).trans v.2.2.1,fun i hi=>(m 5 _ (by decide) (by decide)).trans (v.2.2.2 i hi)⟩
  have pts:=hd.ready.1 Axis.points
  have blocks:=hd.ready.1 Axis.blocks
  change s.ptrs 0=(x.n:ℤ) at pts
  change s.ptrs 1=(x.k:ℤ) at blocks
  have rows:=hd.ready.1 Axis.rows
  change s.ptrs 2=(x.rows:ℤ) at rows
  refine ⟨by simpa [t,perform,saveCounts,Op.eval] using pts,by simpa [t,perform,saveCounts,Op.eval] using blocks,
    ?_,?_,retains _ _ _ past.seed0,retains _ _ _ past.seed1,?_,?_,?_⟩
  · simp [perform,saveCounts,Op.eval,word,hd.gate]
  · simp [perform,saveCounts,Op.eval,word,rows]
  · intro r hr;dsimp only;intro j hj;exact retains _ _ _ (past.blocks r hr j hj)
  · intro p ha hb;exact retains _ _ _ (past.padding p ha hb)
  · intro r hr
    obtain ⟨v,l⟩:=past.dirs r hr
    rw [m 4 r (by decide) (by decide),m 6 r (by decide) (by decide),v,l]
    by_cases h0:r<x.rows*x.n <;> simp [wanted,h0]

def controller (call : Request→Cmd) : Cmd := .seq beginProgram (.seq (emit call .seed)
  (.seq (.whileDo slotGuard (emit call .region)) (.seq (.whileDo padGuard (emit call .pad))
  (.seq (.whileDo tailGuard (emit call .absent)) (line saveCounts)))))

theorem controller_run (x : World) (h w T : ℕ) (call : Request→Cmd) (run : Runs x h w T call) (s : Store)
    (ready : Ready x s) :
    ∃t z,Executes x.dist (controller call) s t z ∧ z≤(T+40)*(x.n+4*total x h w+1) ∧ Reports x h w t := by
  let R:=x.rows*x.n
  let raw:=firstGate x h w R
  let G:=total x h w
  obtain ⟨a,init,head⟩:=begin_run x s ready
  obtain ⟨b,zb,eg,tb,hb,wb⟩:=emit_run x h w T call run .seed 0 0 a head (by intro e;cases e)
  obtain ⟨c,zc,ec,tc,hc,pc⟩:=real_slots x h w T call run b hb (seed_past x h w a b wb)
  obtain ⟨d,zd,ed,td,hd,pd⟩:=padding_slots x h w T call run c hc pc
  obtain ⟨v,zv,ev,tv,hv,pv⟩:=absent_slots x h w T call run d hd pd
  refine ⟨perform x.dist v saveCounts,_,.seq init (.seq eg (.seq ec (.seq ed (.seq ev (line_exec x.dist v _))))),?_,
    finish_reports x h w v hv pv⟩
  change zc≤2+R*(T+10) at tc
  change zd≤2+(G-raw)*(T+10) at td
  change zv≤2+(3*G-R)*(T+10) at tv
  change 8+4*x.n+(zb+(zc+(zd+(zv+4)))) ≤ (T+40)*(x.n+4*G+1)
  have rle:R≤3*G:=by dsimp [R,G,total];omega
  have terms:R+(G-raw)+(3*G-R)≤4*G:=by omega
  have k:=Nat.mul_le_mul_right (T+10) terms
  simp only [Nat.add_mul] at k
  calc _ ≤ 26+4*x.n+T+4*G*(T+10) := by omega
       _ ≤ _ := by nlinarith [Nat.zero_le (T*x.n)]

theorem reports_of_packet_generator
    (size : ∀(x : World) (e : ℚ),0<e → e<1 → 2≤x.n →
      let G:=total x (budget (e:ℝ)) (widthBound (e:ℝ))
      82+42*G+7*(G*x.n)≤256*x.cap^3*x.n^(75*parameterEnvelope (e:ℝ)))
    (packets : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃call:Request→Cmd,PacketGenerator e c D b call) :
    ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,GeneratesReports e c D b cmd := by
  obtain ⟨c,D,b,gen⟩:=packets
  refine ⟨(c+40)*258,D+3,b+75,?_⟩
  intro e he hl
  obtain ⟨call,localRun⟩:=gen e he hl
  refine ⟨controller call,?_⟩
  intro x s hk hn md rd
  let E:=parameterEnvelope (e:ℝ)
  let B:=x.cap^D*x.n^(b*E)
  let A:=x.cap^3*x.n^(75*E)
  let G:=total x (budget (e:ℝ)) (widthBound (e:ℝ))
  have cp:1≤x.cap:=by unfold World.cap;omega
  have npos:1≤x.n:=by omega
  have Bpos:1≤B:=Nat.mul_pos (Nat.pow_pos cp) (Nat.pow_pos npos)
  have Apos:1≤A:=Nat.mul_pos (Nat.pow_pos cp) (Nat.pow_pos npos)
  have run : Runs x (budget (e:ℝ)) (widthBound (e:ℝ)) (c*B) call := by
    intro q r p u head valid
    obtain ⟨t,z,go,tm,ok⟩:=localRun x u hk hn md head.ready q r p head.slot head.gate valid
    exact ⟨t,z,go,by simpa only [B,E,Nat.mul_assoc] using tm,ok⟩
  obtain ⟨t,z,go,tm,done⟩:=controller_run x _ _ _ call run s rd
  refine ⟨t,z,go,tm.trans ?_,done⟩
  have bounds:82+42*G+7*(G*x.n)≤256*A:=by
    simpa only [A,E,G,Nat.mul_assoc] using size x e he hl (by omega)
  have nx:x.n≤A:=by
    have capN:x.n≤x.cap:=by dsimp [World.cap];omega
    calc x.n ≤ x.cap^1 := by simpa using capN
         _ ≤ x.cap^3 := Nat.pow_le_pow_right cp (by decide)
         _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.pow_pos npos)
  have first:c*B+40≤(c+40)*B:=by rw [Nat.add_mul];omega
  have second:x.n+4*G+1≤258*A:=by omega
  apply (Nat.mul_le_mul first second).trans
  change ((c+40)*(x.cap^D*x.n^(b*E)))*(258*(x.cap^3*x.n^(75*E)))≤
    ((c+40)*258)*x.cap^(D+3)*x.n^((b+75)*E)
  rw [Nat.add_mul b 75,pow_add,pow_add]
  exact le_of_eq (by ring)

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit Machine
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def putOps (j idx : ℕ) (v : ℤ) : List Op := [
  .pointerAdd 20 idx idx,.pointerAdd 20 20 20,.pointerAdd 20 20 20,
  .pointerConst 21 (-(32+(j:ℤ))),.pointerSub 20 21 20,.pointerConst 21 v,.integerStore 20 21]
theorem put_run {n : ℕ} (d : Point n→Point n→ℝ) (s : Store) (j idx a : ℕ) (v : ℤ)
    (arg : s.ptrs idx=(a:ℤ)) :
    let t:=perform d s (putOps j idx v)
    (∀r<20,t.ptrs r=s.ptrs r) ∧ ∀q,t.imem q=if q=word j a then v else s.imem q := by
  dsimp only
  refine ⟨?_,?_⟩
  · intro r hr;simp [perform,putOps,Op.eval,Function.update_of_ne (by omega:r≠20),Function.update_of_ne (by omega:r≠21)]
  · intro q
    have ad:-(32+(j:ℤ))-(((a:ℤ)+a+(a+a))+((a+a)+(a+a)))=word j a:=by unfold word;ring
    simp only [putOps,perform,Op.eval,Function.update_self,Function.update_of_ne (by decide:20≠21),arg,ad,Function.update_apply]

def cleared (s t : Store) (lo i : ℕ) := (∀j < i,t.imem (word 5 (lo+j))=0) ∧
  ∀q:ℤ,(∀j < i,q≠word 5 (lo+j)) → t.imem q=s.imem q
def bitAdvance : List Op := [.pointerInc 14,.pointerDec 15]
def bitBody : Cmd := .seq (line (putOps 5 14 0)) (line bitAdvance)
def bitLoop := Cmd.whileDo (.pointerLE 16 15) bitBody

theorem bit_loop_run (x : World) (s : Store) (lo : ℕ)
    (a : s.ptrs 14=(lo:ℤ)) (cnt : s.ptrs 15=(x.n:ℤ)) (one : s.ptrs 16=1) :
    ∃t z,Executes x.dist bitLoop s t z ∧ z≤2+x.n*11 ∧
      (∀r<10,t.ptrs r=s.ptrs r) ∧ cleared s t lo x.n := by
  let I:=fun i (t:Store)=>t.ptrs 14=(lo+i:ℕ) ∧ t.ptrs 15=(x.n-i:ℕ) ∧ t.ptrs 16=1 ∧
    (∀r<10,t.ptrs r=s.ptrs r) ∧ cleared s t lo i
  have go:=bounded_loop x (.pointerLE 16 15) bitBody I x.n 9 (by
    intro i t h;change t.ptrs 16≤t.ptrs 15 ↔ (i<x.n)
    rw [h.2.2.1,h.2.1];omega) (by
    intro i hi t h
    obtain ⟨atIdx,rem,unit,keep,yes,no⟩:=h
    let u:=perform x.dist t (putOps 5 14 0)
    let v:=perform x.dist u bitAdvance
    obtain ⟨reg,mem⟩:=put_run x.dist t 5 14 (lo+i) 0 atIdx
    have same (r : ℕ) (hr:r<10) : v.ptrs r=s.ptrs r := by
      simpa [v,bitAdvance,perform,Op.eval,Function.update_of_ne (by omega:r≠14),Function.update_of_ne (by omega:r≠15)] using
        (reg r (by omega)).trans (keep r hr)
    refine ⟨v,7+2,.seq (line_exec x.dist t _) (line_exec x.dist u _),by decide,?_,?_,?_,same,?_,?_⟩
    · simp [v,bitAdvance,perform,Op.eval,show u.ptrs 14= t.ptrs 14 from reg 14 (by decide),atIdx];omega
    · simp [v,bitAdvance,perform,Op.eval,show u.ptrs 15= t.ptrs 15 from reg 15 (by decide),rem];omega
    · simpa [v,bitAdvance,perform,Op.eval] using (reg 16 (by decide)).trans unit
    · intro j hj
      change u.imem _=0;rw [mem]
      split
      · rfl
      · next ne=>
          have diff:j≠i:=fun e=>ne (by rw [e])
          exact yes j (by omega)
    · intro q avoid
      change u.imem q=s.imem q
      rw [mem,if_neg (avoid i (by omega))]
      exact no q (fun j hj=>avoid j (by omega))) s (by
    exact ⟨by simpa using a,by simpa using cnt,one,fun _ _=>rfl,fun j hj=>by omega,fun _ _=>rfl⟩)
  obtain ⟨t,z,run,cost,_,_,_,keep,last⟩:=go
  exact ⟨t,z,run,cost,keep,last⟩

def productInit : List Op := [.pointerConst 14 0,.pointerCopy 15 9,.pointerCopy 16 0,.pointerConst 17 1]
def bitInit : List Op := [.pointerCopy 15 0,.pointerConst 16 1]
def eraseBits : Cmd := .seq (line productInit) (.seq (addLoop 14) (.seq (line bitInit) bitLoop))

theorem erase_bits (x : World) (s : Store) (p : ℕ) (pn : s.ptrs 0=(x.n:ℤ)) (arg : s.ptrs 9=(p:ℤ)) :
    ∃t z,Executes x.dist eraseBits s t z ∧ z≤10+15*x.n ∧ (∀r<10,t.ptrs r=s.ptrs r) ∧
      cleared s t (p*x.n) x.n := by
  let a:=perform x.dist s productInit
  have low (r : ℕ) (hr:r<10) : a.ptrs r=s.ptrs r := by
    simp [a,productInit,perform,Op.eval,Function.update_of_ne (by omega:r≠14),Function.update_of_ne (by omega:r≠15),
      Function.update_of_ne (by omega:r≠16),Function.update_of_ne (by omega:r≠17)]
  obtain ⟨b,prod,fr,pval⟩:=addLoop_run x.dist 14 x.n a 0 (p:ℤ)
    (by simp [a,perform,productInit,Op.eval]) (by simp [a,perform,productInit,Op.eval,arg])
    (by simp [a,perform,productInit,Op.eval,pn]) (by simp [a,perform,productInit,Op.eval])
  let c:=perform x.dist b bitInit
  have low' (r : ℕ) (hr:r<10) : c.ptrs r=s.ptrs r:=by
    simpa [c,bitInit,perform,Op.eval,Function.update_of_ne (by omega:r≠15),Function.update_of_ne (by omega:r≠16)]
      using (fr.1 r (by omega)).trans (low r hr)
  obtain ⟨t,z,go,cost,eq,hit,elsewhere⟩:=bit_loop_run x c (p*x.n)
    (by simp [c,bitInit,perform,Op.eval,pval,mul_comm])
    (by simp [c,bitInit,perform,Op.eval,(fr.1 0 (by decide)).trans (low 0 (by decide)),pn])
    (by simp [c,bitInit,perform,Op.eval])
  have m:c.imem=s.imem:=fr.2
  refine ⟨t,4+((2+4*x.n)+(2+z)),.seq (line_exec x.dist s _) (.seq prod (.seq (line_exec x.dist b _) go)),by omega,
    fun r hr=>(eq r hr).trans (low' r hr),hit,?_⟩
  intro q e;rw [elsewhere q e,m]

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit SingleRAM Machine
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 12000

def blank (stop : Bool) : Gate := if stop then .stop else .atom []
def touched (n p : ℕ) (q : ℤ) := q=word 1 p ∨ q=word 2 p ∨ q=word 3 p ∨ ∃i<n,q=word 5 (p*n+i)
def indices (second : Bool) : List Op :=
  [.pointerCopy 9 4] ++ (if second then [.pointerInc 9] else [])
def fields (stop : Bool) : Cmd :=
  .seq (line (putOps 1 9 (opCode (blank stop)))) (.seq (line (putOps 2 9 0)) (line (putOps 3 9 0)))
def blankGate (second stop : Bool) : Cmd := .seq (line (indices second)) (.seq (fields stop) eraseBits)
def off (second : Bool) : ℕ := if second then 1 else 0

theorem fields_run (x : World) (s : Store) (p : ℕ) (stop : Bool) (addr : s.ptrs 9=(p:ℤ)) :
    ∃t,Executes x.dist (fields stop) s t 21 ∧ (∀r<20,t.ptrs r=s.ptrs r) ∧
      ∀q,t.imem q=if q=word 3 p then 0 else if q=word 2 p then 0 else if q=word 1 p then opCode (blank stop) else s.imem q := by
  let a:=perform x.dist s (putOps 1 9 (opCode (blank stop)))
  let b:=perform x.dist a (putOps 2 9 0)
  let c:=perform x.dist b (putOps 3 9 0)
  obtain ⟨ka,ma⟩:=put_run x.dist s 1 9 p (opCode (blank stop)) addr
  obtain ⟨kb,mb⟩:=put_run x.dist a 2 9 p 0 ((ka 9 (by decide)).trans addr)
  obtain ⟨kc,mc⟩:=put_run x.dist b 3 9 p 0 ((kb 9 (by decide)).trans ((ka 9 (by decide)).trans addr))
  refine ⟨c,.seq (line_exec x.dist s _) (.seq (line_exec x.dist a _) (line_exec x.dist b _)),
    fun r hr=>(kc r hr).trans ((kb r hr).trans (ka r hr)),?_⟩
  intro q;change (perform x.dist b (putOps 3 9 0)).imem q=_
  rw [mc,mb,ma]

theorem blank_gate_run (x : World) (s : Store) (p : ℕ) (second stop : Bool)
    (pn : s.ptrs 0=(x.n:ℤ)) (gate : s.ptrs 4=(p:ℤ)) :
    let P:=p+off second
    ∃t z,Executes x.dist (blankGate second stop) s t z ∧ z≤33+15*x.n ∧
      (∀r<8,t.ptrs r=s.ptrs r) ∧ (∀j,Record x.n t P j (blank stop)) ∧
      ∀q,¬touched x.n P q → t.imem q=s.imem q := by
  let P:=p+off second
  let a:=perform x.dist s (indices second)
  have pos:a.ptrs 9=(P:ℤ):=by cases second <;> simp [P,off,a,indices,perform,Op.eval,gate]
  have low (r : ℕ) (hr:r<8) : a.ptrs r=s.ptrs r:=by
    cases second <;> simp [a,indices,perform,Op.eval,Function.update_of_ne (by omega:r≠9)]
  have cells:a.imem=s.imem:=by cases second <;> rfl
  obtain ⟨b,run,regs,mem⟩:=fields_run x a P stop pos
  obtain ⟨t,z,go,work,keep,hit,avoid⟩:=erase_bits x b P ((regs 0 (by decide)).trans ((low 0 (by decide)).trans pn))
    ((regs 9 (by decide)).trans pos)
  have head (j : ℕ) (hj : j<5) : t.imem (word j P)=b.imem (word j P) := by
    apply avoid;intro i hi;rw [ne_eq,word_inj (by omega) (by decide)];omega
  have h1 : t.imem (word 1 P)=opCode (blank stop):=by
    rw [head 1 (by decide),mem];simp [word_inj (by decide : 1<8) (by decide : 3<8),
      word_inj (by decide : 1<8) (by decide : 2<8)]
  have h2 : t.imem (word 2 P)=0:=by
    rw [head 2 (by decide),mem];simp [word_inj (by decide : 2<8) (by decide : 3<8)]
  have h3 : t.imem (word 3 P)=0:=by rw [head 3 (by decide),mem];simp
  have len:(indices second).length≤2:=by cases second <;> decide
  refine ⟨t,(indices second).length+(21+z),.seq (line_exec x.dist s _) (.seq run go),by omega,
    fun r hr=>(keep r (by omega)).trans ((regs r (by omega)).trans (low r hr)),?_,?_⟩
  · intro j
    refine ⟨h1,?_,?_,?_⟩
    · cases stop <;> simpa [blank,displacement,opCode,leftID] using h2
    · cases stop <;> simpa [blank,displacement,opCode,rightID] using h3
    · intro i hi;cases stop <;> simpa [blank,tinyMask] using hit i hi
  · intro q nq
    have a1:q≠word 1 P:=fun e=>nq (Or.inl e)
    have a2:q≠word 2 P:=fun e=>nq (Or.inr (Or.inl e))
    have a3:q≠word 3 P:=fun e=>nq (Or.inr (Or.inr (Or.inl e)))
    rw [avoid q (fun i hi e=>nq (Or.inr (Or.inr (Or.inr ⟨i,hi,e⟩)))),mem,if_neg a3,if_neg a2,if_neg a1,cells]

theorem preserve_gate {n p a j : ℕ} {op : Gate} {s t : Store}
    (same : ∀q,¬touched n p q → t.imem q=s.imem q) (lt : a<p) (old : Record n s a j op) : Record n t a j op := by
  have point (k : ℕ) (hk : k<4) : t.imem (word k a)=s.imem (word k a) := by
    apply same;unfold touched
    simp [word_inj (by omega : k<8) (by decide : 1<8),word_inj (by omega : k<8) (by decide : 2<8),
      word_inj (by omega : k<8) (by decide : 3<8),word_inj (by omega : k<8) (by decide : 5<8),
      Nat.ne_of_lt lt,show k≠5 by omega]
  refine ⟨(point 1 (by decide)).trans old.1,(point 2 (by decide)).trans old.2.1,(point 3 (by decide)).trans old.2.2.1,?_⟩
  intro i hi
  apply Eq.trans (same _ ?_) (old.2.2.2 i hi)
  unfold touched
  have sep:=Nat.mul_le_mul_right n (show a+1≤p by omega)
  rw [Nat.add_mul,Nat.one_mul] at sep
  simp only [word_inj (by decide : 5<8) (by decide : 1<8),word_inj (by decide : 5<8) (by decide : 2<8),
    word_inj (by decide : 5<8) (by decide : 3<8),word_inj (by decide : 5<8) (by decide : 5<8)]
  omega

theorem preserve_dir {n p a : ℕ} {v : ℤ×ℕ} {s t : Store}
    (same : ∀q,¬touched n p q → t.imem q=s.imem q) (old : DirAt s a v) : DirAt t a v := by
  have no (j : ℕ) (hj : j=4 ∨ j=6) : ¬touched n p (word j a) := by
    rcases hj with rfl|rfl <;> simp [touched,word_inj (by decide : 4<8),word_inj (by decide : 6<8)]
  exact ⟨(same _ (no _ (Or.inl rfl))).trans old.1,(same _ (no _ (Or.inr rfl))).trans old.2⟩

theorem preserve_ready {x : World} {p : ℕ} {s t : Store} (rd : Ready x s)
    (regs : ∀r<8,t.ptrs r=s.ptrs r) (same : ∀q,¬touched x.n p q → t.imem q=s.imem q) : Ready x t := by
  refine ⟨fun ax=>(regs _ (by cases ax <;> decide)).trans (rd.1 ax),?_⟩
  intro i
  apply (same _ ?_).trans (rd.2 i)
  unfold touched word
  push_neg;constructor
  · omega
  · constructor
    · omega
    · constructor
      · omega
      · intro a ha;omega

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative.Controller
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP Machine
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000

def blankPacket : Request→Cmd
  | .seed=>.seq (blankGate false false) (blankGate true true)
  | .pad=>blankGate false true
  | .absent=>.seq (line (putOps 4 3 (-1))) (line (putOps 6 3 0))
  | .region=>.skip
def fixedLength : Request→ℕ | .seed=>2 | .pad=>1 | _=>0
def constCall (q : Request) := Cmd.seq (blankPacket q) (.atom (.pointerConst 7 (fixedLength q)))

theorem absent_write (x : World) (h w r p : ℕ) (s : Store) (rd : Ready x s) (slot : s.ptrs 3=(r:ℤ)) :
    ∃t,Executes x.dist (blankPacket .absent) s t 14 ∧ Ready x t ∧ (∀a<8,t.ptrs a=s.ptrs a) ∧
      Writes x h w r p .absent s t := by
  let a:=perform x.dist s (putOps 4 3 (-1))
  let t:=perform x.dist a (putOps 6 3 0)
  obtain ⟨ka,ma⟩:=put_run x.dist s 4 3 r (-1) slot
  obtain ⟨kt,mt⟩:=put_run x.dist a 6 3 r 0 ((ka 3 (by decide)).trans slot)
  have mem (z : ℤ) : t.imem z=if z=word 6 r then 0 else if z=word 4 r then -1 else s.imem z := by
    change (perform x.dist a (putOps 6 3 0)).imem z=_
    rw [mt,ma]
  have low (a : ℕ) (ha : a<8) : t.ptrs a=s.ptrs a:=(kt a (by omega)).trans (ka a (by omega))
  have gate (j i : ℕ) (hj : j<8) (a : j≠4) (b : j≠6) : t.imem (word j i)=s.imem (word j i) := by
    rw [mem];simp [word_inj hj (by decide : 4<8),word_inj hj (by decide : 6<8),a,b]
  have keep (a : ℕ) (lt : a<r) (j : ℕ) (hj:j<8) : t.imem (word j a)=s.imem (word j a) := by
    rw [mem];simp [word_inj hj (by decide : 4<8),word_inj hj (by decide : 6<8),Nat.ne_of_lt lt]
  refine ⟨t,.seq (line_exec x.dist s _) (line_exec x.dist a _),⟨fun ax=>(low _ (by cases ax <;> decide)).trans (rd.1 ax),?_⟩,
    low,⟨?_,?_,?_,?_⟩⟩
  · intro i;rw [mem,if_neg (by unfold word;omega),if_neg (by unfold word;omega),rd.2]
  · intro j hj;change j<0 at hj;omega
  · intro v hv;change some ((-1:ℤ),0)=some v at hv;cases hv
    constructor <;> rw [mem] <;> simp [word_inj (by decide : 4<8) (by decide : 6<8)]
  · intro a ha j op o
    exact ⟨(gate 1 _ (by decide) (by decide) (by decide)).trans o.1,(gate 2 _ (by decide) (by decide) (by decide)).trans o.2.1,
      (gate 3 _ (by decide) (by decide) (by decide)).trans o.2.2.1,
      fun i hi=>(gate 5 _ (by decide) (by decide) (by decide)).trans (o.2.2.2 i hi)⟩
  · intro a ha v o;exact ⟨(keep a ha 4 (by decide)).trans o.1,(keep a ha 6 (by decide)).trans o.2⟩

theorem fixed_write (x : World) (h w r p : ℕ) (q : Request) (s : Store) (rd : Ready x s)
    (slot : s.ptrs 3=(r:ℤ)) (base : s.ptrs 4=(p:ℤ)) (fixed : q≠.region) :
    ∃t z,Executes x.dist (blankPacket q) s t z ∧ z≤70+30*x.n ∧ Ready x t ∧
      (∀a<8,t.ptrs a=s.ptrs a) ∧ Writes x h w r p q s t := by
  have pn:s.ptrs 0=(x.n:ℤ):=rd.1 .points
  cases q with
  | region=>exact (fixed rfl).elim
  | absent=>
    obtain ⟨t,go,ready,regs,out⟩:=absent_write x h w r p s rd slot
    exact ⟨t,14,go,by omega,ready,regs,out⟩
  | pad=>
    obtain ⟨t,z,go,tm,regs,gate,fr⟩:=blank_gate_run x s p false true pn base
    change ∀q,¬touched x.n p q → t.imem q=s.imem q at fr
    refine ⟨t,z,go,by omega,preserve_ready rd regs fr,regs,⟨?_,?_,?_,?_⟩⟩
    · intro j hj
      change j<1 at hj
      have e:j=0:=by omega
      subst j
      exact gate 0
    · intro v hv;cases hv
    · intro a ha j op old;exact preserve_gate fr ha old
    · intro a ha v old;exact preserve_dir fr old
  | seed=>
    obtain ⟨a,z,ea,za,ka,ga,fa⟩:=blank_gate_run x s p false false pn base
    change ∀q,¬touched x.n p q → a.imem q=s.imem q at fa
    obtain ⟨t,l,et,zt,kt,gt,ft⟩:=blank_gate_run x a p true true ((ka 0 (by decide)).trans pn) ((ka 4 (by decide)).trans base)
    change ∀q,¬touched x.n (p+1) q → t.imem q=a.imem q at ft
    refine ⟨t,z+l,.seq ea et,by omega,preserve_ready (preserve_ready rd ka fa) kt ft,
      fun i hi=>(kt i hi).trans (ka i hi),⟨?_,?_,?_,?_⟩⟩
    · intro j hj;change j<2 at hj
      interval_cases j
      · exact preserve_gate ft (show p<p+1 by omega) (ga 0)
      · exact gt 1
    · intro v hv;cases hv
    · intro a ha j op old;exact preserve_gate ft (by omega) (preserve_gate fa ha old)
    · intro a ha v old;exact preserve_dir ft (preserve_dir fa old)

theorem const_call_run (x : World) (h w r p : ℕ) (q : Request) (s : Store) (rd : Ready x s)
    (slot : s.ptrs 3=(r:ℤ)) (base : s.ptrs 4=(p:ℤ)) (fixed : q≠.region) :
    ∃t z,Executes x.dist (constCall q) s t z ∧ z≤128*(1+x.n) ∧ PacketCall x h w r p q s t := by
  obtain ⟨a,z,go,cost,ready,regs,out⟩:=fixed_write x h w r p q s rd slot base fixed
  let o:=Op.pointerConst 7 (fixedLength q)
  let t:=o.eval x.dist a
  have eq:fixedLength q=(payload x h w r q).size:=by cases q <;> first | rfl | contradiction
  refine ⟨t,z+1,.seq go (.atom o a),by omega,⟨⟨?_,ready.2⟩,?_,?_,out.gates,out.dir,out.oldGate,out.oldDir⟩⟩
  · intro ax
    have neq:ax.reg≠7:=by cases ax <;> decide
    simpa [t,o,Op.eval,Function.update_of_ne neq] using ready.1 ax
  · intro i hi
    have lt:i<7:=by simp at hi;omega
    simpa [t,o,Op.eval,Function.update_of_ne (by omega : i≠7)] using regs i (by omega)
  · simp [t,o,Op.eval,eq]

theorem packets_of_region
    (region : ∃ c D b : ℕ, ∀e : ℚ, 0<e → e<1 → ∃cmd:Cmd,
      ∀(x : World) (s : Store), 1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
      ∀r p : ℕ, s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
      ∃t z, Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
        PacketCall x (budget (e:ℝ)) (widthBound (e:ℝ)) r p .region s t) :
    ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃call:Request→Cmd,PacketGenerator e c D b call := by
  obtain ⟨c,D,b,make⟩:=region
  refine ⟨c+128,D+1,b,?_⟩
  intro e he hl
  obtain ⟨cmd,src⟩:=make e he hl
  let call : Request→Cmd := fun q=>match q with | .region=>cmd | q=>constCall q
  refine ⟨call,?_⟩
  intro x s hk kn met rd q r p slot base valid
  have cp:1≤x.cap:=by dsimp [World.cap];omega
  have xp:1≤x.n^(b*parameterEnvelope (e:ℝ)):=Nat.pow_pos (by omega)
  by_cases real:q=.region
  · subst q
    obtain ⟨t,z,go,tm,ok⟩:=src x s hk kn met rd r p slot base (valid rfl)
    refine ⟨t,z,go,tm.trans ?_,ok⟩
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right cp (by omega)))
  · have eq:call q=constCall q:=by cases q <;> first | rfl | contradiction
    obtain ⟨t,z,go,tm,ok⟩:=const_call_run x _ _ r p q s rd slot base real
    refine ⟨t,z,eq.symm ▸ go,tm.trans ?_,ok⟩
    have lo:1+x.n≤x.cap:=by dsimp [World.cap];omega
    have cap:x.cap≤x.cap^(D+1):=by simpa using Nat.pow_le_pow_right cp (show 1≤D+1 by omega)
    exact (Nat.mul_le_mul (by omega : 128≤c+128) (lo.trans cap)).trans (Nat.le_mul_of_pos_right _ xp)

end StableMSR.Recovery.CanonicalWriter.Relative.Controller

namespace StableMSR.Recovery.CanonicalWriter.Relative
open Compiler OracleQueries SingleRAM WindowCSP
set_option autoImplicit false

theorem writer_from_regional_reports
    (source : ∃ c D b : ℕ, ∀ e : ℚ, 0<e → e<1 → ∃ cmd : Cmd, GeneratesReports e c D b cmd) :
    ∃ c D b : ℕ, 0<c ∧ 0<b ∧ ∀ e : ℚ, 0<e → e<1 → ∃ cmd : Cmd, StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.NativeSpec e c D b cmd := by
  apply writer_of_columns
  apply columns_of_reports _ native_relative_relocation_pass source
  intro x e he hl hn
  exact (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.global_assembly_resource_bound x e he hl hn).2.2

theorem writer_from_packet_calls
    (packets : ∃ c D b : ℕ, ∀ e : ℚ, 0<e → e<1 →
      ∃ call : Request→Cmd, PacketGenerator e c D b call) :
    ∃ c D b : ℕ, 0<c ∧ 0<b ∧ ∀ e : ℚ, 0<e → e<1 → ∃ cmd : Cmd, StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.NativeSpec e c D b cmd := by
  apply writer_from_regional_reports
  apply Controller.reports_of_packet_generator _ packets
  intro x e he hl hn
  rw [←total_size]
  exact (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.global_assembly_resource_bound x e he hl hn).2.2

theorem writer_from_single_region
    (region : ∃ c D b : ℕ, ∀e : ℚ, 0<e → e<1 → ∃cmd:Cmd,
      ∀(x : World) (s : Store), 1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
      ∀r p : ℕ, s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
      ∃t z, Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
        PacketCall x (budget (e:ℝ)) (widthBound (e:ℝ)) r p .region s t) :
    ∃ c D b : ℕ, 0<c ∧ 0<b ∧ ∀ e : ℚ, 0<e → e<1 → ∃ cmd : Cmd, StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.NativeSpec e c D b cmd :=
  writer_from_packet_calls (Controller.packets_of_region region)

end StableMSR.Recovery.CanonicalWriter.Relative

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP
theorem dense_of_writer (sem:∀(x:World)(e:ℚ),0<x.n →
  let a:=Canonical.assembly x (budget (e:ℝ)) (widthBound (e:ℝ));RegionalLanguage x e a.gates a.roots)
  (w:∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃p:Cmd,NativeSpec e c D b p) :
  ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃p:Cmd,denseSpec e c D b p:=by
  obtain ⟨c,D,b,cp,bp,run⟩:=w
  refine ⟨c,D,b,cp,bp,?_⟩
  intro e he hl
  obtain ⟨p,ok⟩:=run e he hl
  refine ⟨p,?_⟩
  intro x s hk kn metric ready
  obtain ⟨t,z,H,run,cost,space,rd,rows,room,inp⟩:=ok x s hk kn metric ready
  exact ⟨t,z,H,run,cost,space,rd,rows,_,_,room,inp,sem x e (by omega)⟩
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical

namespace StableMSR.Recovery.NativeWriter.Production.Candidates
open SingleCircuit SingleCodes TightLanguage OracleQueries WindowCSP
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1400000

theorem tape_envelope (enc:Key→ℕ) (d:Instance) (w K B:ℕ) (hn:0<d.n) (hk:0<K)
    (menu:∀v,(d.menu v).length≤K) (mask:∀v x,(d.owned v x).length≤B) :
    (tape enc d w).length≤gateEnvelope d.n K B w := by
  let vs:=vertices d
  let cuts' := cuts vs (min w d.n)
  let F:=d.n*K*(2*B+d.n+2)
  have nv:vs.length≤d.n:=(List.length_filter_le ..).trans (by simp)
  have nc:cuts'.length≤(d.n+1)^w:=(cuts_count vs _).trans ((Nat.pow_le_pow_left (by omega:vs.length+1≤d.n+1) _).trans
    (Nat.pow_le_pow_right (by omega) (Nat.min_le_left ..)))
  have nc' (s:List ℕ) : (keysFor d vs s).length≤d.n:=(parts_count d _).trans ((List.length_filter_le ..).trans nv)
  have tr (c:List ℕ) (a:Assignment) (v x:ℕ) (hc:c.length≤d.n) :
      (trial enc d c a v x).length≤B+d.n+1:=by
    have n: (children d c v ((v,x)::a)).length≤d.n:=by
      simpa only [children,List.length_map] using (parts_count d (c.erase v)).trans ((List.length_erase_le ..).trans hc)
    have m:=mask v x
    simp only [trial,List.length_append,List.length_map,List.length_singleton];omega
  have row (c:List ℕ) (a:Assignment) (hc:c.length≤d.n) : (entry enc d c a).length≤F:=by
    have per (v:ℕ) : ((d.menu v).flatMap (trial enc d c a v)).length≤K*(B+d.n+1) :=
      (flat_length _ _ _ (fun x _=>tr c a v x hc)).trans (Nat.mul_le_mul_right _ (menu v))
    have all: (c.flatMap (fun v=>(d.menu v).flatMap (trial enc d c a v))).length≤d.n*(K*(B+d.n+1)) :=
      (flat_length _ _ _ (fun v _=>per v)).trans (Nat.mul_le_mul_right _ hc)
    have pos:1≤d.n*K:=Nat.mul_pos hn hk
    simp only [entry,List.length_append,List.length_singleton];dsimp [F]
    rw [←Nat.mul_assoc] at all;nlinarith [Nat.zero_le (d.n*K*B)]
  have visitL (k:ℕ) (s c:List ℕ) (hs:s.length≤w) (h:k<d.n) :
      (visitTape enc d k s c).length≤K^w*F:=by
    unfold visitTape;split
    · next yes=>
        have len:c.length=k+1:=by simp only [Bool.and_eq_true,beq_iff_eq] at yes;exact yes.1
        apply (flat_length _ _ F (fun a _=>row c a (by omega))).trans
        exact Nat.mul_le_mul_right F ((assignments_bound d K menu s).trans (Nat.pow_le_pow_right hk hs))
    · simp
  have component (k:ℕ) (s:List ℕ) (h:k<d.n) (hs:s∈cuts') :
      ((keysFor d vs s).flatMap (visitTape enc d k s)).length≤d.n*(K^w*F):=
    (flat_length _ _ _ (fun c _=>visitL k s c ((cut_size vs _ s hs).trans (Nat.min_le_left ..)) h)).trans
      (Nat.mul_le_mul_right _ (nc' s))
  have cutRow (k:ℕ) (h:k<d.n) : (cuts'.flatMap (fun s=>(keysFor d vs s).flatMap (visitTape enc d k s))).length≤
      (d.n+1)^w*(d.n*(K^w*F)):=
    (flat_length _ _ _ (fun s hs=>component k s h hs)).trans (Nat.mul_le_mul_right _ nc)
  have rows : (rowTape enc d w).length≤d.n*((d.n+1)^w*(d.n*(K^w*F))):=by
    simpa only [rowTape,vs,cuts',List.length_range] using
      (flat_length (List.range d.n) (fun k=>cuts'.flatMap (fun s=>(keysFor d vs s).flatMap (visitTape enc d k s))) _
        (fun k h=>cutRow k (List.mem_range.mp h)))
  have nroot: (parts d vs).length≤d.n := (parts_count d vs).trans nv
  simp only [tape,List.length_append,List.length_map,List.length_singleton,gateEnvelope]
  change (rowTape enc d w).length+(parts d vs).length+1≤_
  simp only [Nat.mul_assoc] at rows ⊢
  dsimp [F] at rows
  simp only [Nat.mul_assoc] at rows
  omega

end StableMSR.Recovery.NativeWriter.Production.Candidates
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge
open SingleCircuit SingleCodes TightLanguage OracleQueries WindowCSP
open scoped Classical
theorem scene_envelope (x:World) (W:Cluster x.n) (R:ℝ) (h w:ℕ) (enc:Key→ℕ) (hn:1≤x.n) :
    (tape enc (arrange (instanceOf x W R h)) w).length≤gateEnvelope x.n (menuLimit x.n h) x.n w := by
  let K := menuLimit x.n h
  have pos : 0<K := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have words : (SingleCodes.words x.n h).length ≤ K := by
    apply (flat_length _ _ (CartesianBallRows.rows x.n (h+1)) ?_).trans
    · simp [K,menuLimit,CartesianBallRows.rows]
    · intro a ha; simp
  apply tape_envelope enc (arrange (instanceOf x W R h)) w K x.n hn pos
  · intro v
    simp only [arrange,Canonical.blockList,List.length_mergeSort,List.length_map,SingleCodes.instanceOf,SingleCodes.lookup]
    split
    · exact (List.length_filter_le ..).trans words
    · simp
  · intro v a
    simp only [arrange,Canonical.blockList,List.length_mergeSort,List.length_map,SingleCodes.instanceOf,SingleCodes.lookup]
    split
    · simp only [SingleCodes.blockList,List.length_map,Finset.length_toList]
      apply (Finset.card_filter_le ..).trans
      apply Finset.card_image_le.trans
      simpa using (Finset.card_le_univ (WindowCSP.window x.dist W R ⟨v,by assumption⟩))
    · simp


theorem regional_bound (x:World) (u i:ℕ) (e:ℚ) (enc:Key→ℕ) (he:0<e) (hl:e<1) (hn:2≤x.n) :
    (tape enc (arrange (instanceOf x (WindowProfiles.piece x u i) (scale x u) (budget (e:ℝ)))) (widthBound (e:ℝ))).length≤x.n^(75*parameterEnvelope (e:ℝ)) := by
  have realPos:0<(e:ℝ):=by exact_mod_cast he
  have realLt:(e:ℝ)<1:=by exact_mod_cast hl
  have ow:1≤ownerBound (e:ℝ) := by
    unfold ownerBound
    apply Nat.le_floor
    push_cast
    exact (le_div_iff₀ realPos).2 (by linarith)
  apply (scene_envelope x _ _ _ _ enc (by omega)).trans
  apply (envelope_power _ _ _ hn).trans
  apply Nat.pow_le_pow_right (by omega)
  have b:WindowCSP.budget (e:ℝ)+1≤5*ownerBound (e:ℝ):=by unfold WindowCSP.budget;omega
  have c:=Nat.mul_le_mul_right (widthBound (e:ℝ)+1) b
  unfold parameterEnvelope
  nlinarith

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge
open Compiler OracleQueries WindowCSP
def Source (e : ℚ) (c D b : ℕ) (cmd : Cmd) : Prop :=
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    Stored x.n t.imem (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script x (budget (e:ℝ)) (widthBound (e:ℝ)) r)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge
open OracleQueries WindowCSP SingleCircuit SingleCodes Relative TightLanguage
theorem script_exact (x : World) (h w r : ℕ) : (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script x h w r).packet=StableMSR.Recovery.CanonicalWriter.Relative.packet x h w r := by
  unfold StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script StableMSR.Recovery.CanonicalWriter.Relative.packet;dsimp only
  split
  · split
    · unfold Script.packet
      simp only [Int.natCast_nonneg,not_lt.mpr,if_false,Int.toNat_natCast]
      let d:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.arrange (instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) h)
      have eq:=StableMSR.Recovery.NativeWriter.Production.ordered_production_replay d w
      change Packet.mk (result (chart d w)).1 ((result (chart d w)).2:ℤ)=
        Packet.mk (compileRegion d w).1 ((compileRegion d w).2:ℤ)
      rw [eq]
    · rfl
  · rfl

theorem script_length (x : World) (e : ℚ) (r:ℕ) (he:0<e) (hl:e<1) (hn:2≤x.n) :
    (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script x (budget (e:ℝ)) (widthBound (e:ℝ)) r).events.length≤x.n^(75*parameterEnvelope (e:ℝ)) := by
  unfold StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script;dsimp only
  split
  · split
    · exact (chart_length _ _).trans (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.uniform_live_gate_bound x _ _ e he hl hn)
    · exact Nat.zero_le _
  · exact Nat.zero_le _

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry 
open Compiler OracleQueries WindowCSP SingleCircuit
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem transfer {n:ℕ} {d:Fin n→Fin n→ℝ} (g:Fin n→Fin n→ℝ) {c:Cmd} {s t:Store} {z:ℕ}
    (ex:Executes d c s t z) (h:IntegerCmd c) : Executes g c s t z := by
  induction ex with
  | skip=>exact .skip _
  | atom o s=> cases o <;> first | exact .atom _ _ | contradiction
  | seq _ _ ih jh=>exact .seq (ih h.1) (jh h.2)
  | ite_true cond _ ih=>exact .ite_true cond (ih h.2.1)
  | ite_false cond _ ih=>exact .ite_false cond (ih h.2.2)
  | while_false cond=>exact .while_false cond
  | while_true cond _ _ ih jh=>exact .while_true cond (ih h.2) (jh h)

theorem word_ne_table (j a i:ℕ) (lo:1≤j) (hi:j≤6) : word j a≠cell 6 i:=by
  intro eq;unfold cell word at eq;push_cast at eq;omega

theorem compose (integerSource : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,IntegerCmd cmd ∧
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes (fun (_ _:Fin x.n)=>(0:ℝ)) cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      Input x.n t.imem (tape enc (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)))) (nativeTable : ∃cmd:Cmd,∀(x:World) (s:Store),Ready x s → 0<x.n → ∀r:ℕ,s.ptrs 3=(r:ℤ) → r<x.rows*x.n →
    ∃t z,Executes x.dist cmd s t z ∧
      z≤200*(1+x.rows+(1+x.n*x.n)^2) ∧ t.queries=s.queries+x.n*x.n+1 ∧
      Ready x t ∧ (∀j<6,t.ptrs j=s.ptrs j) ∧
      (∀q:ℤ,(∀j:ℕ,q≠cell 6 j) → t.imem q=s.imem q) ∧ Prepared x (scale x (r/x.n)) t.imem)
    (canon:∀(x:World) (r h:ℕ) (m:ℤ→ℤ),0<x.n → 0<scale x (r/x.n) → IsMetricArray x.dist → Prepared x (scale x (r/x.n)) m → StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.integerData x.n x.mem m r h=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.arrange (SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) h))
    (exactTable : ∀(x:World) (W:Cluster x.n) (R:ℝ) (h:ℕ) (m:ℤ→ℤ)
    (hn:0<x.n) (pos:0<R) (metric:IsMetricArray x.dist) (t:Prepared x R m) ,
    SingleCodes.instanceOf (matrix x m) W (unit x.n:ℝ) h=SingleCodes.instanceOf x W R h ∧ Bounded x.n m) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      let d:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.arrange (SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) (budget (e:ℝ)))
      Input x.n t.imem (tape enc d (widthBound (e:ℝ))) := by
  obtain ⟨c,D,b,generate⟩:=integerSource
  obtain ⟨pre,preOK⟩:=nativeTable
  refine ⟨1200+c,D+4,b,?_⟩
  intro e he hl
  obtain ⟨cmd,pure,run⟩:=generate e he hl
  refine ⟨.seq pre cmd,?_⟩
  intro x s hk kn metric rd r p slot off live key pos
  have hn:0<x.n:=by omega
  obtain ⟨u,y,ey,cy,queries,ru,ptr,frame,table⟩:=preOK x s rd hn r slot live
  have eq:=exactTable x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) (budget (e:ℝ)) u.imem hn pos metric table
  obtain ⟨v,z,ez,cz,rv,regs,words,enc,inj,tapeOK⟩:=run x u hk kn ru eq.2 r p
    ((ptr 3 (by decide)).trans slot) ((ptr 4 (by decide)).trans off) live key
  refine ⟨v,y+z,.seq ey (transfer x.dist ez pure),?_,rv,?_,?_,enc,inj,?_⟩
  · let E:=x.n^(b*parameterEnvelope (e:ℝ))
    have cp:1≤x.cap:=by unfold World.cap;omega
    have nc:x.n≤x.cap:=by unfold World.cap;omega
    have rows:x.rows≤x.cap:=by unfold World.cap;omega
    have c2:1≤x.cap^2:=Nat.one_le_pow _ _ cp
    have c4:1≤x.cap^4:=Nat.one_le_pow _ _ cp
    have c14:x.cap≤x.cap^4:=by simpa using (Nat.pow_le_pow_right (n:=x.cap) cp (show 1≤4 by decide))
    have n2:x.n*x.n≤x.cap^2:=by simpa [pow_two] using Nat.mul_le_mul nc nc
    have box:1+x.n*x.n≤2*x.cap^2:=by omega
    have sq: (1+x.n*x.n)^2≤4*x.cap^4:=calc
      _≤(2*x.cap^2)^2:=Nat.pow_le_pow_left box _
      _=4*x.cap^4:=by ring
    have py:y≤1200*x.cap^4:=by omega
    have small:x.cap^4≤x.cap^(D+4):=Nat.pow_le_pow_right cp (by omega)
    have large:x.cap^D≤x.cap^(D+4):=Nat.pow_le_pow_right cp (by omega)
    have ee:1≤E:=Nat.one_le_pow _ _ hn
    have left:y≤1200*x.cap^(D+4)*E:=by
      have h:=Nat.mul_le_mul (Nat.mul_le_mul_left 1200 small) ee
      exact py.trans (by simpa using h)
    have right:z≤c*x.cap^(D+4)*E:=cz.trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left c large))
    simpa only [Nat.add_mul] using Nat.add_le_add left right
  · intro j hj;exact (regs j hj).trans (ptr j (by simp at hj;omega))
  · intro j lo hi a;exact (words j lo hi a).trans (frame _ (word_ne_table j a · lo hi))
  · simpa only [canon x r _ u.imem hn pos metric table] using tapeOK

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge
open StableMSR.Recovery.NativeWriter.Production.Candidates 
open Compiler OracleQueries WindowCSP SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000
theorem live_from_raw (raw : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      let d:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.arrange (SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) (budget (e:ℝ)))
      Input x.n t.imem (tape enc d (widthBound (e:ℝ))))
    (native : ∃ (A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (xs:List Candidates.Instr),Ready x s → Input x.n s.imem xs →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+xs.length) ∧ Ready x t ∧
      (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧ (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
      Stored x.n t.imem (Candidates.eval xs))
    (exactScan : ∀(enc:Key→ℕ),Function.Injective enc → ∀(d:Instance) (w:ℕ),Candidates.eval (tape enc d w)=⟨(chart d w).1,((chart d w).2:ℤ)⟩)
    (limit : ∀(x:World) (u i:ℕ) (e:ℚ) (enc:Key→ℕ),0<e → e<1 → 2≤x.n →
      (tape enc (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.arrange (SingleCodes.instanceOf x (WindowProfiles.piece x u i) (scale x u) (budget (e:ℝ)))) (widthBound (e:ℝ))).length≤x.n^(75*parameterEnvelope (e:ℝ))) :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    Stored x.n t.imem (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script x (budget (e:ℝ)) (widthBound (e:ℝ)) r) := by
  obtain ⟨c,D,b,raw⟩:=raw
  obtain ⟨A,filter,filterOK⟩:=native
  refine ⟨c+2*A,D+1,b+75,?_⟩
  intro e he hl
  obtain ⟨emit,emitOK⟩:=raw e he hl
  refine ⟨.seq emit filter,?_⟩
  intro x s k kn metric rd r p slot off actual key live
  let d:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.arrange (SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) (budget (e:ℝ)))
  let w:=widthBound (e:ℝ)
  obtain ⟨t,z,first,cost,ready,regs,mem,enc,inj,buf⟩:=emitOK x s k kn metric rd r p slot off actual key live
  let xs:=tape enc d w
  obtain ⟨v,y,second,bound,endReady,low,cols,stored⟩:=filterOK x t xs ready buf
  have matchTable:Candidates.eval xs=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script x (budget (e:ℝ)) w r:=by
    simpa only [StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script,key,live,ite_true,d,w,xs] using exactScan enc inj d w
  rw [matchTable] at stored
  refine ⟨v,z+y,.seq first second,?_,endReady,fun j hj=>(low j hj).trans (regs j hj),
    fun j a b k=>(cols j a b k).trans (mem j a b k),stored⟩
  have sz:=limit x (r/x.n) (r%x.n) e enc he hl (by omega)
  change xs.length≤_ at sz
  let E:=parameterEnvelope (e:ℝ)
  have hc:1≤x.cap:=by unfold World.cap;omega
  have nc:1+x.n≤x.cap:=by unfold World.cap;omega
  have hn:1≤x.n:=by omega
  have pow1:1≤x.n^(75*E):=Nat.one_le_pow _ _ hn
  have size:1+xs.length≤2*x.n^(75*E):=by change xs.length≤x.n^(75*E) at sz;omega
  have d1:x.cap^D≤x.cap^(D+1):=Nat.pow_le_pow_right hc (by omega)
  have d2:x.cap≤x.cap^(D+1):=by simpa using (Nat.pow_le_pow_right (n:=x.cap) hc (show 1≤D+1 by omega))
  have e1:x.n^(b*E)≤x.n^((b+75)*E):=Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E (by omega))
  have e2:x.n^(75*E)≤x.n^((b+75)*E):=Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E (by omega))
  have left:=cost.trans (Nat.mul_le_mul (Nat.mul_le_mul_left c d1) e1)
  have right:y≤(2*A)*x.cap^(D+1)*x.n^((b+75)*E):=calc
    y ≤ A*(1+x.n)*(1+xs.length) := bound
    _ ≤ A*x.cap^(D+1)*(2*x.n^(75*E)) := Nat.mul_le_mul (Nat.mul_le_mul_left A (nc.trans d2)) size
    _ = (2*A)*x.cap^(D+1)*x.n^(75*E) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ e2
  simpa only [Nat.add_mul] using Nat.add_le_add left right
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge
open Compiler OracleQueries WindowCSP WindowProfiles StableMSR.Recovery.CanonicalWriter.Relative.Machine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1400000

noncomputable def kind (x:World) (r:ℕ) : ℤ :=
  if r%x.n∈keys x (r/x.n) then if 0<scale x (r/x.n) then 0 else -2 else -1

theorem word_ne_cell {a i j k:ℕ} (hk:k<7) : word k j≠cell a i:=by
  intro h;unfold cell word at h;push_cast at h;omega

/-- The absent and stopped encodings consist of two header words. -/
def header : List Op := [.pointerConst 27 (cell 0 0),.pointerConst 28 0,.integerStore 27 28,
  .pointerConst 27 (cell 0 1),.integerStore 27 6]

theorem empty_script (x:World) (h w r:ℕ) (hs:kind x r<0) : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script x h w r=⟨[],kind x r⟩ := by
  by_cases key:r%x.n∈keys x (r/x.n)
  · by_cases live:0<scale x (r/x.n)
    · simp [kind,key,live] at hs
    · simp [StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script,kind,key,live]
  · simp [StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script,kind,key]

theorem live_of_sign (x:World) (r:ℕ) (hs:¬kind x r≤-1) : r%x.n∈keys x (r/x.n) ∧ 0<scale x (r/x.n) := by
  by_cases key:r%x.n∈keys x (r/x.n)
  · by_cases live:0<scale x (r/x.n)
    · exact ⟨key,live⟩
    · simp [kind,key,live] at hs
  · simp [kind,key] at hs

theorem header_run (x:World) (s:Store) (h w r:ℕ) (rd:Ready x s) (v:s.ptrs 6=kind x r) (hs:kind x r<0) :
    let t:=perform x.dist s header
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    Stored x.n t.imem (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script x h w r) := by
  let t:=perform x.dist s header
  have regs (i:ℕ) (hi:i<27) : t.ptrs i=s.ptrs i:=by
    simp [t,header,perform,Op.eval,Function.update_of_ne (by omega:i≠27),Function.update_of_ne (by omega:i≠28)]
  have mem (q:ℤ) : t.imem q=if q=cell 0 1 then kind x r else if q=cell 0 0 then 0 else s.imem q:=by
    simp [t,header,perform,Op.eval,Function.update_apply,v]
  refine ⟨⟨fun ax=>(regs _ (by cases ax <;> decide)).trans (rd.1 ax),?_⟩,?_,?_,?_⟩
  · intro q;rw [mem,if_neg (by unfold cell word;omega),if_neg (by unfold cell word;omega),rd.2]
  · intro i hi;exact regs i (by simp at hi;omega)
  · intro j lo hi a;rw [mem];simp [word_ne_cell (by omega:j<7)]
  · rw [empty_script x h w r hs]
    exact ⟨by rw [mem];simp [cell,word],by rw [mem];simp,fun i hi=>by simp at hi⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge
open Compiler OracleQueries WindowCSP WindowProfiles StableMSR.Recovery.CanonicalWriter.Relative.Machine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

theorem source_from_live (input:∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  r%x.n∈WindowProfiles.keys x (r/x.n) → 0<scale x (r/x.n) →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    Stored x.n t.imem (StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script x (budget (e:ℝ)) (widthBound (e:ℝ)) r))
    (detect:∃ (A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (r:ℕ),Ready x s → s.ptrs 3=(r:ℤ) → 0<x.n → r<x.rows*x.n →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+x.rows) ∧ t.imem=s.imem ∧
      (∀i<6,t.ptrs i=s.ptrs i) ∧
      t.ptrs 6=(if r%x.n∈WindowProfiles.keys x (r/x.n) then if 0<scale x (r/x.n) then 0 else -2 else -1) ∧
      t.ptrs 14 = -1) :
    ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,Source e c D b cmd := by
  obtain ⟨c,D,b,offer⟩:=input
  obtain ⟨A,test,scan⟩:=detect
  refine ⟨A+c+8,D+2,b,?_⟩
  intro e he hl
  obtain ⟨live,guarantee⟩:=offer e he hl
  refine ⟨.seq test (.ite (.pointerLE 6 14) (line header) live),?_⟩
  intro x s k kn metric rd r p slot offset actual
  obtain ⟨t,z,go,cost,mem,low,sign,minus⟩:=scan x s r rd slot (by omega) actual
  change t.ptrs 6=kind x r at sign
  have ready:Ready x t:=⟨fun ax=>(low _ (by cases ax <;> decide)).trans (rd.1 ax),fun q=>(congrFun mem _).trans (rd.2 q)⟩
  have ts: t.ptrs 3=(r:ℤ):=(low 3 (by decide)).trans slot
  have tp: t.ptrs 4=(p:ℤ):=(low 4 (by decide)).trans offset
  have testEq:(Cond.pointerLE 6 14).test t ↔ kind x r≤-1:=by change t.ptrs 6 ≤ t.ptrs 14 ↔ _;rw [sign,minus]
  let phi:=x.cap^(D+2)*x.n^(b*parameterEnvelope (e:ℝ))
  have cap:1≤x.cap:=by unfold World.cap;omega
  have npos:1≤x.n:=by omega
  have pow:1≤x.n^(b*parameterEnvelope (e:ℝ)):=Nat.one_le_pow _ _ npos
  have cp:x.cap^2≤x.cap^(D+2):=Nat.pow_le_pow_right cap (by omega)
  have d:x.cap^D≤x.cap^(D+2):=Nat.pow_le_pow_right cap (by omega)
  have cat: (1+x.n)*(1+x.rows)≤phi:=calc
    _ ≤ x.cap*x.cap := Nat.mul_le_mul (by unfold World.cap;omega) (by unfold World.cap;omega)
    _ = x.cap^2 := by ring
    _ ≤ phi := cp.trans (Nat.le_mul_of_pos_right _ pow)
  have left:z≤A*phi:= (by simpa only [Nat.mul_assoc] using cost : z≤A*((1+x.n)*(1+x.rows))).trans (Nat.mul_le_mul_left _ cat)
  have one:1≤phi:=by nlinarith [cat,Nat.zero_le (x.n*x.rows)]
  have target:(A+c+8)*x.cap^(D+2)*x.n^(b*parameterEnvelope (e:ℝ))=(A+c+8)*phi:=by simp only [phi,Nat.mul_assoc]
  by_cases dead:kind x r≤-1
  · let v:=perform x.dist t header
    obtain ⟨fin,regs,lanes,out⟩:=header_run x t (budget (e:ℝ)) (widthBound (e:ℝ)) r ready sign (by omega)
    refine ⟨v,_,.seq go (.ite_true (testEq.mpr dead) (line_exec x.dist t _)),?_,fin,?_,?_,out⟩
    · rw [target];change z+(1+5)≤_;nlinarith
    · intro i hi;exact (regs i hi).trans (low i (by simp at hi;omega))
    · intro j lo hi a;exact (lanes j lo hi a).trans (congrFun mem _)
  · obtain ⟨key,pos⟩:=live_of_sign x r dead
    obtain ⟨v,y,compiled,time,fin,regs,lanes,out⟩:=guarantee x t k kn metric ready r p ts tp actual key pos
    refine ⟨v,_,.seq go (.ite_false (fun h=>dead (testEq.mp h)) compiled),?_,fin,?_,?_,out⟩
    · have right:y≤c*phi:=by
        apply time.trans
        calc c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ≤ c*x.cap^(D+2)*x.n^(b*parameterEnvelope (e:ℝ)) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c d)
             _ = c*phi := by simp [phi,Nat.mul_assoc]
      rw [target];nlinarith
    · intro i hi;exact (regs i hi).trans (low i (by simp at hi;omega))
    · intro j lo hi a;exact (lanes j lo hi a).trans (congrFun mem _)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge
open StableMSR.Recovery.NativeWriter.Production 
open Compiler OracleQueries SingleCircuit WindowCSP Relative
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

theorem source_frame {n : ℕ} {s t : Store} (h:∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a))
    {a j : ℕ} {op:Gate} (o:Record n s a j op) : Record n t a j op :=
  ⟨(h 1 (by decide) (by decide) a).trans o.1,(h 2 (by decide) (by decide) a).trans o.2.1,
    (h 3 (by decide) (by decide) a).trans o.2.2.1,fun k hk=>(h 5 (by decide) (by decide) _).trans (o.2.2.2 k hk)⟩

theorem from_production_source
    (src:∃ c D b : ℕ,∀e : ℚ,0<e → e<1 → ∃cmd : Cmd, Source e c D b cmd)
    (decoderLaw:∃ (A : ℕ) (cmd : Cmd),∀(x : World) (s : Store) (r p : ℕ) (a : Script),
    Ready x s → s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → Stored x.n s.imem a →
    ∃t z, Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+a.events.length) ∧
      Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧ t.ptrs 7=(a.packet.gates.size:ℤ) ∧
      (∀j<a.packet.gates.size, Record x.n t (p+j) j (gateAt a.packet.gates j)) ∧
      DirAt t r (a.packet.token,a.packet.gates.size) ∧
      (∀q<p,∀j op,Record x.n s q j op → Record x.n t q j op) ∧
      ∀q<r,∀v,DirAt s q v → DirAt t q v)
    (regional:∀(x:World) (e:ℚ) (r:ℕ),0<e → e<1 → 2≤x.n →
      let h:=budget (e:ℝ);let w:=widthBound (e:ℝ);let a:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script x h w r
      a.packet=StableMSR.Recovery.CanonicalWriter.Relative.packet x h w r ∧ a.events.length≤x.n^(75*parameterEnvelope (e:ℝ))) :
    ∃ c D b : ℕ, ∀e : ℚ, 0<e → e<1 → ∃cmd:Cmd,
      ∀(x : World) (s : Store), 1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
      ∀r p : ℕ, s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
      ∃t z, Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
        StableMSR.Recovery.CanonicalWriter.Relative.PacketCall x (budget (e:ℝ)) (widthBound (e:ℝ)) r p .region s t := by


  obtain ⟨c,D,b,source⟩:=src
  obtain ⟨A,decode,dr⟩:=decoderLaw
  refine ⟨c+2*A,D+1,b+75,?_⟩
  intro e he hl
  obtain ⟨enumerate,en⟩:=source e he hl
  refine ⟨.seq enumerate decode,?_⟩
  intro x s k kn metric rd r p slot off actual
  let h:=budget (e:ℝ)
  let w:=widthBound (e:ℝ)
  let a:=StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.script x h w r
  obtain ⟨t,z,first,cost,ready,regs,mem,table⟩:=en x s k kn metric rd r p slot off actual
  obtain ⟨v,y,second,bound,endReady,low,last,gates,dir,older,dirs⟩:=dr x t r p a ready
    ((regs 3 (by simp)).trans slot) ((regs 4 (by simp)).trans off) table
  obtain ⟨eq,sz⟩:=regional x e r he hl (by omega)
  change a.packet=StableMSR.Recovery.CanonicalWriter.Relative.packet x h w r at eq
  change a.events.length≤_ at sz
  rw [eq] at last gates dir
  refine ⟨v,z+y,.seq first second,?_,⟨endReady,fun i hi=>(low i hi).trans (regs i hi),last,gates,?_,?_,?_⟩⟩
  · let E:=parameterEnvelope (e:ℝ)
    have hc:1≤x.cap:=by unfold World.cap;omega
    have nc:1+x.n≤x.cap:=by unfold World.cap;omega
    have hn:1≤x.n:=by omega
    have pow1:1≤x.n^(75*E):=Nat.one_le_pow _ _ hn
    have size:1+a.events.length≤2*x.n^(75*E):=by change a.events.length≤x.n^(75*E) at sz;omega
    have d1:x.cap^D≤x.cap^(D+1):=Nat.pow_le_pow_right hc (by omega)
    have d2:x.cap≤x.cap^(D+1):=by simpa using (Nat.pow_le_pow_right (n:=x.cap) hc (show 1≤D+1 by omega))
    have e1:x.n^(b*E)≤x.n^((b+75)*E):=Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E (by omega))
    have e2:x.n^(75*E)≤x.n^((b+75)*E):=Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E (by omega))
    have left:=cost.trans (Nat.mul_le_mul (Nat.mul_le_mul_left c d1) e1)
    have right:y≤(2*A)*x.cap^(D+1)*x.n^((b+75)*E):=calc
      y ≤ A*(1+x.n)*(1+a.events.length) := bound
      _ ≤ A*x.cap^(D+1)*(2*x.n^(75*E)) := Nat.mul_le_mul (Nat.mul_le_mul_left A (nc.trans d2)) size
      _ = (2*A)*x.cap^(D+1)*x.n^(75*E) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ e2
    simpa only [Nat.add_mul] using Nat.add_le_add left right
  · intro b hb;change some ((StableMSR.Recovery.CanonicalWriter.Relative.packet x h w r).token,(StableMSR.Recovery.CanonicalWriter.Relative.packet x h w r).gates.size)=some b at hb
    cases hb;exact dir
  · intro q hq j op o;exact older q hq j op (source_frame mem o)
  · intro q hq b o;exact dirs q hq b ⟨(mem 4 (by decide) (by decide) q).trans o.1,(mem 6 (by decide) (by decide) q).trans o.2⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.Bridge
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.dense_of_native_source (source : ∃c D b:ℕ,∀e:ℚ,0<e → e<1 → ∃cmd:Cmd,IntegerCmd cmd ∧
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃t z,Executes (fun (_ _:Fin x.n)=>(0:ℝ)) cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    ∃enc:Key→ℕ,Function.Injective enc ∧
      Input x.n t.imem (tape enc (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)))) : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,SingleRAM.denseSpec e c D b cmd := by
  apply Canonical.dense_of_writer Canonical.assembly_recognizes_original
  apply StableMSR.Recovery.CanonicalWriter.Relative.writer_from_single_region
  apply Canonical.Bridge.from_production_source _ Production.native_chart_packet_decoder
    (fun x e r he hl hn=>⟨Canonical.Bridge.script_exact x _ _ r,Canonical.Bridge.script_length x e r he hl hn⟩)
  apply Canonical.Bridge.source_from_live _ Production.native_slot_classification
  apply Canonical.Bridge.live_from_raw _ Candidates.native_candidate_filter Candidates.unfiltered_scan_is_exact Canonical.Bridge.regional_bound
  exact Canonical.Bridge.compose source native_metric_table Canonical.computed_integer_instance integer_instance_exact
end WriterBridge

/- Original mission reduction: StableMSR.Recovery.SingleWindows.emit_singleton_separator_grammar
   https://prove2.me/theorems/6deb6492-8944-41d4-b2ff-ecede0ed1584
   Accepted sketch 619d15d1-dc30-4261-abd6-97a8152c010f. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage0
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleCircuit
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.WindowProfiles (subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Writes field)
open StableMSR.Recovery.SingleRAM
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)
open Polynomial
private lemma powerBound (p : Polynomial ℕ) : ∃C T : ℕ,0< T ∧ ∀v : ℕ,1≤ v → p.eval v≤ C*v^T:=by
  classical
  let T:=p.natDegree+1
  refine ⟨∑i∈Finset.range T,p.coeff i,T,by dsimp [T];omega,?_⟩
  intro v hv;rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv (Finset.mem_range.mp hi).le))
theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,nativeSpec e c D b cmd := by
  obtain ⟨c,D,b,cp,bp,build⟩:=dense
  obtain ⟨P,solve,run⟩:=native_circuit_record_emitter
  obtain ⟨C,T,tp,major⟩:=powerBound P
  refine ⟨(C+1)*(c+1)^T,(D+1)*T,b*T,Nat.mul_pos (by omega) (pow_pos (by omega) _),Nat.mul_pos bp tp,?_⟩
  intro e ep el;obtain ⟨make,construct⟩:=build e ep el
  refine ⟨make.seq solve,?_⟩
  intro x s hk kn metric ready
  obtain ⟨a,l,H,ea,time,height,ar,scene,g,roots,size,encoded,lang⟩:=construct x s hk kn metric ready
  let y:=worldOf x.k H x.dist a
  obtain ⟨t,j,et,pol,rd,head,rep⟩:=run y a g roots hk (by change 0< x.n;omega) size ar encoded
  let out:=worldOf x.k H x.dist t
  have prof : Implements x e out:=by
    refine ⟨rep.1,head.trans scene,?_⟩;intro u hu i hi
    obtain ⟨index,valid,unused,dry,live⟩:=lang.2.2 u hu i hi
    have eq:=(rep.2.2 (u*x.n+i) index).2.2.2.1
    change (board out).root (u*x.n+i)=roots (u*x.n+i) at eq
    have vol : (board out).size=3*g.size:=rep.2.1
    have equiv (L : List (Cluster x.n)) := native_board_realizes_circuit_language out g roots rep lang.1 lang.2.1 (roots (u*x.n+i)) L
    change u*x.n+i<(board out).size ∧ (board out).root (u*x.n+i)<(board out).size ∧ _
    rw [eq,vol];refine ⟨index,valid,?_,?_,?_⟩
    · intro no L;exact (equiv L).trans (unused no L)
    · intro key nonpos L tr;exact dry key nonpos L ((equiv L).mp tr)
    · intro key pos;refine ⟨fun L tr=>(live key pos).1 L ((equiv L).mp tr),?_⟩
      intro Q gen;obtain ⟨L,hl,eL⟩:=(live key pos).2 Q gen
      exact ⟨L,(equiv L).mpr hl,eL⟩
  let E:=parameterEnvelope (e:ℝ);let V:=x.cap;let N:=x.n^(b*E)
  let B:=(c+1)*V^(D+1)*N
  have vp : 1≤ V:=by dsimp [V,World.cap];omega
  have np : 1≤ N:=Nat.one_le_pow _ _ (by omega)
  have one : 1≤ V^(D+1):=Nat.one_le_pow _ _ vp
  have up : V^D≤ V^(D+1):=Nat.pow_le_pow_right vp (by omega)
  have ve : V≤ V^(D+1):=by simpa only [pow_one] using Nat.pow_le_pow_right vp (show 1≤ D+1 by omega)
  have scale : V≤ V^(D+1)*N:=ve.trans (Nat.le_mul_of_pos_right _ np)
  have lim : c*V^D*N≤ c*V^(D+1)*N:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ up)
  have beq : B=c*V^(D+1)*N+V^(D+1)*N:=by dsimp [B];ring
  have old : l≤ B:=by change l≤ c*V^D*N at time;omega
  have extra : H≤ c*V^(D+1)*N:=height.trans lim
  have cover : y.cap≤ V+H:=by dsimp [y,V,worldOf,World.cap];omega
  have big : y.cap≤ B:=by omega
  have Bpos : 1≤ B:=by omega
  have Bup : B≤ B^T:=by simpa only [pow_one] using Nat.pow_le_pow_right Bpos (show 1≤ T by omega)
  have yp : 1≤ y.cap:=by dsimp [World.cap];omega
  have later : j≤ C*B^T:=pol.trans ((major _ yp).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left big _)))
  have polyEq : (C+1)*B^T=(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E):=by
    dsimp only [B,N];simp only [mul_pow,←pow_mul];rw [show b*E*T=b*T*E by ring];ring
  have hB : H≤ B:=by omega
  refine ⟨t,_,H,.seq ea et,?_,?_,rd,prof⟩
  rotate_left
  · change H≤(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E);rw [←polyEq]
    exact (hB.trans Bup).trans (Nat.le_mul_of_pos_left _ (by omega))
  change l+j≤(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E)
  calc l+j≤ B^T+C*B^T:=Nat.add_le_add (old.trans Bup) later
       _=(C+1)*B^T:=by ring
       _=_:=by dsimp only [B,N];simp only [mul_pow,←pow_mul];rw [show b*E*T=b*T*E by ring];ring
end StableMSRCompiledRecoveryStage0

/- Original mission reduction: StableMSR.Recovery.WindowMasks.native_regional_block_incidences
   https://prove2.me/theorems/fb867983-5d9e-48d6-8f4d-22822e4df7c4
   Accepted sketch d3f9af5c-249f-408c-a586-750c9010b5e7. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage1
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.Supplement
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)
theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,maskSpec e c D b cmd := by
  obtain ⟨c,D,b,cp,bp,source⟩:=(StableMSRCompiledRecoveryStage0.fromDense dense)
  refine ⟨c,D,b,cp,bp,?_⟩;intro e ep el
  obtain ⟨cmd,run⟩:=source e ep el
  refine ⟨cmd,?_⟩;intro x s hk hn dm ready
  obtain ⟨t,z,H,ex,time,space,out,sem⟩:=run x s hk hn dm ready
  exact ⟨t,z,H,ex,time,space,out,singleton_board_describes_regional_incidences _ _ _ dm sem⟩
end StableMSRCompiledRecoveryStage1

/- Original mission reduction: StableMSR.Recovery.WindowPorts.native_separator_ports
   https://prove2.me/theorems/2301bbed-0665-446f-a523-ff50ed19d6c6
   Accepted sketch eae89390-435e-4af0-969b-260ed07ea43a. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage2
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowMasks
open Polynomial
private lemma powerBound (p : Polynomial ℕ) : ∃C T : ℕ,0< T ∧ ∀v : ℕ,1≤ v → p.eval v≤ C*v^T:=by
  classical
  let T:=p.natDegree+1
  refine ⟨∑i∈Finset.range T,p.coeff i,T,by dsimp [T];omega,?_⟩
  intro v hv;rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv (Finset.mem_range.mp hi).le))
theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,portSpec e c D b cmd := by
  obtain ⟨c,D,b,cp,bp,build⟩:=(StableMSRCompiledRecoveryStage1.fromDense dense)
  obtain ⟨P,solve,run⟩:=native_block_literal_compiler
  obtain ⟨C,T,tp,major⟩:=powerBound P
  refine ⟨(C+1)*(c+1)^T,(D+1)*T,b*T,Nat.mul_pos (by omega) (pow_pos (by omega) _),Nat.mul_pos bp tp,?_⟩
  intro e ep el;obtain ⟨make,construct⟩:=build e ep el
  refine ⟨make.seq solve,?_⟩
  intro x s hk kn metric ready
  obtain ⟨a,l,H,ea,time,height,ar,cert⟩:=construct x s hk kn metric ready
  let y:=worldOf x.k H x.dist a
  obtain ⟨t,j,et,pol,rd,prof⟩:=run x e H a hk kn metric ar cert
  let E:=parameterEnvelope (e:ℝ);let V:=x.cap;let N:=x.n^(b*E)
  let B:=(c+1)*V^(D+1)*N
  have vp : 1≤ V:=by dsimp [V,World.cap];omega
  have np : 1≤ N:=Nat.one_le_pow _ _ (by omega)
  have one : 1≤ V^(D+1):=Nat.one_le_pow _ _ vp
  have up : V^D≤ V^(D+1):=Nat.pow_le_pow_right vp (by omega)
  have ve : V≤ V^(D+1):=by simpa only [pow_one] using Nat.pow_le_pow_right vp (show 1≤ D+1 by omega)
  have scale : V≤ V^(D+1)*N:=ve.trans (Nat.le_mul_of_pos_right _ np)
  have lim : c*V^D*N≤ c*V^(D+1)*N:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ up)
  have beq : B=c*V^(D+1)*N+V^(D+1)*N:=by dsimp [B];ring
  have old : l≤ B:=by change l≤ c*V^D*N at time;omega
  have extra : H≤ c*V^(D+1)*N:=height.trans lim
  have cover : y.cap≤ V+H:=by dsimp [y,V,worldOf,World.cap];omega
  have big : y.cap≤ B:=by omega
  have Bpos : 1≤ B:=by omega
  have Bup : B≤ B^T:=by simpa only [pow_one] using Nat.pow_le_pow_right Bpos (show 1≤ T by omega)
  have yp : 1≤ y.cap:=by dsimp [World.cap];omega
  have later : j≤ C*B^T:=pol.trans ((major _ yp).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left big _)))
  have polyEq : (C+1)*B^T=(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E):=by
    dsimp only [B,N];simp only [mul_pow,←pow_mul];rw [show b*E*T=b*T*E by ring];ring
  have hB : H≤ B:=by omega
  refine ⟨t,_,H,.seq ea et,?_,?_,rd,prof⟩
  rotate_left
  · change H≤(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E);rw [←polyEq]
    exact (hB.trans Bup).trans (Nat.le_mul_of_pos_left _ (by omega))
  change l+j≤(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E)
  calc l+j≤ B^T+C*B^T:=Nat.add_le_add (old.trans Bup) later
       _=(C+1)*B^T:=by ring
       _=_:=by dsimp only [B,N];simp only [mul_pow,←pow_mul];rw [show b*E*T=b*T*E by ring];ring
end StableMSRCompiledRecoveryStage2

/- Original mission reduction: StableMSR.Recovery.WindowJoins.native_window_join_records
   https://prove2.me/theorems/058fddd8-64f6-46c8-9d8c-5b73bde7dd9a
   Accepted sketch 2483f793-fe95-4285-9bcd-c54e7e3f165c. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage3
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open Polynomial
private lemma powerBound (p : Polynomial ℕ) : ∃C T : ℕ,0< T ∧ ∀v : ℕ,1≤ v → p.eval v≤ C*v^T:=by
  classical
  let T:=p.natDegree+1
  refine ⟨∑i∈Finset.range T,p.coeff i,T,by dsimp [T];omega,?_⟩
  intro v hv;rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv (Finset.mem_range.mp hi).le))
theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,buildSpec e c D b cmd := by
  obtain ⟨c,D,b,cp,bp,build⟩:=(StableMSRCompiledRecoveryStage2.fromDense dense)
  obtain ⟨P,solve,run⟩:=native_count_expansion
  obtain ⟨C,T,tp,major⟩:=powerBound P
  refine ⟨(C+1)*(c+1)^T,(D+1)*T,b*T,Nat.mul_pos (by omega) (pow_pos (by omega) _),Nat.mul_pos bp tp,?_⟩
  intro e ep el;obtain ⟨make,construct⟩:=build e ep el
  refine ⟨make.seq solve,?_⟩
  intro x s hk kn metric ready
  obtain ⟨a,l,H,ea,time,height,ar,cert⟩:=construct x s hk kn metric ready
  let y:=worldOf x.k H x.dist a
  obtain ⟨t,j,et,pol,rd,prof⟩:=run x e H a hk kn ar cert
  let E:=parameterEnvelope (e:ℝ);let V:=x.cap;let N:=x.n^(b*E)
  let B:=(c+1)*V^(D+1)*N
  have vp : 1≤ V:=by dsimp [V,World.cap];omega
  have np : 1≤ N:=Nat.one_le_pow _ _ (by omega)
  have one : 1≤ V^(D+1):=Nat.one_le_pow _ _ vp
  have up : V^D≤ V^(D+1):=Nat.pow_le_pow_right vp (by omega)
  have ve : V≤ V^(D+1):=by simpa only [pow_one] using Nat.pow_le_pow_right vp (show 1≤ D+1 by omega)
  have scale : V≤ V^(D+1)*N:=ve.trans (Nat.le_mul_of_pos_right _ np)
  have lim : c*V^D*N≤ c*V^(D+1)*N:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ up)
  have beq : B=c*V^(D+1)*N+V^(D+1)*N:=by dsimp [B];ring
  have old : l≤ B:=by change l≤ c*V^D*N at time;omega
  have extra : H≤ c*V^(D+1)*N:=height.trans lim
  have cover : y.cap≤ V+H:=by dsimp [y,V,worldOf,World.cap];omega
  have big : y.cap≤ B:=by omega
  have Bpos : 1≤ B:=by omega
  have Bup : B≤ B^T:=by simpa only [pow_one] using Nat.pow_le_pow_right Bpos (show 1≤ T by omega)
  have yp : 1≤ y.cap:=by dsimp [World.cap];omega
  have later : j≤ C*B^T:=pol.trans ((major _ yp).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left big _)))
  have polyEq : (C+1)*B^T=(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E):=by
    dsimp only [B,N];simp only [mul_pow,←pow_mul];rw [show b*E*T=b*T*E by ring];ring
  have hB : H≤ B:=by omega
  refine ⟨t,_,H,.seq ea et,?_,?_,rd,prof⟩
  rotate_left
  · change H≤(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E);rw [←polyEq]
    exact (hB.trans Bup).trans (Nat.le_mul_of_pos_left _ (by omega))
  change l+j≤(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E)
  calc l+j≤ B^T+C*B^T:=Nat.add_le_add (old.trans Bup) later
       _=(C+1)*B^T:=by ring
       _=_:=by dsimp only [B,N];simp only [mul_pow,←pow_mul];rw [show b*E*T=b*T*E by ring];ring
end StableMSRCompiledRecoveryStage3

/- Original mission reduction: StableMSR.Recovery.WindowProfiles.native_single_region_profiles
   https://prove2.me/theorems/b80d089a-e04d-4f66-82ba-a08a7990cb2e
   Accepted sketch a69029ee-86b1-4056-8d5a-f9f60122e687. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage4
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open Polynomial
private lemma powerBound (p : Polynomial ℕ) : ∃C T : ℕ,0< T ∧ ∀v : ℕ,1≤ v → p.eval v≤ C*v^T:=by
  classical
  let T:=p.natDegree+1
  refine ⟨∑i∈Finset.range T,p.coeff i,T,by dsimp [T];omega,?_⟩
  intro v hv;rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  exact Finset.sum_le_sum (fun i hi=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv (Finset.mem_range.mp hi).le))
theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,profileSpec e c D b cmd := by
  obtain ⟨c,D,b,cp,bp,build⟩:=(StableMSRCompiledRecoveryStage3.fromDense dense)
  obtain ⟨P,solve,run⟩:=native_join_decoder
  obtain ⟨C,T,tp,major⟩:=powerBound P
  refine ⟨(C+1)*(c+1)^T,(D+1)*T,b*T,Nat.mul_pos (by omega) (pow_pos (by omega) _),Nat.mul_pos bp tp,?_⟩
  intro e ep el;obtain ⟨make,construct⟩:=build e ep el
  refine ⟨make.seq solve,?_⟩
  intro x s hk kn metric ready
  obtain ⟨a,l,H,ea,time,height,ar,cert⟩:=construct x s hk kn metric ready
  let y:=worldOf x.k H x.dist a
  obtain ⟨t,j,et,pol,rd,prof⟩:=run x e H a hk (by omega) ar cert
  let E:=parameterEnvelope (e:ℝ);let V:=x.cap;let N:=x.n^(b*E)
  let B:=(c+1)*V^(D+1)*N
  have vp : 1≤ V:=by dsimp [V,World.cap];omega
  have np : 1≤ N:=Nat.one_le_pow _ _ (by omega)
  have one : 1≤ V^(D+1):=Nat.one_le_pow _ _ vp
  have up : V^D≤ V^(D+1):=Nat.pow_le_pow_right vp (by omega)
  have ve : V≤ V^(D+1):=by simpa only [pow_one] using Nat.pow_le_pow_right vp (show 1≤ D+1 by omega)
  have scale : V≤ V^(D+1)*N:=ve.trans (Nat.le_mul_of_pos_right _ np)
  have lim : c*V^D*N≤ c*V^(D+1)*N:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ up)
  have beq : B=c*V^(D+1)*N+V^(D+1)*N:=by dsimp [B];ring
  have old : l≤ B:=by change l≤ c*V^D*N at time;omega
  have extra : H≤ c*V^(D+1)*N:=height.trans lim
  have cover : y.cap≤ V+H:=by dsimp [y,V,worldOf,World.cap];omega
  have big : y.cap≤ B:=by omega
  have Bpos : 1≤ B:=by omega
  have Bup : B≤ B^T:=by simpa only [pow_one] using Nat.pow_le_pow_right Bpos (show 1≤ T by omega)
  have yp : 1≤ y.cap:=by dsimp [World.cap];omega
  have later : j≤ C*B^T:=pol.trans ((major _ yp).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left big _)))
  refine ⟨t,_,.seq ea et,?_,rd,prof⟩
  change l+j≤(C+1)*(c+1)^T*V^((D+1)*T)*x.n^((b*T)*E)
  calc l+j≤ B^T+C*B^T:=Nat.add_le_add (old.trans Bup) later
       _=(C+1)*B^T:=by ring
       _=_:=by dsimp only [B,N];simp only [mul_pow,←pow_mul];rw [show b*E*T=b*T*E by ring];ring
end StableMSRCompiledRecoveryStage4

/- Original mission reduction: StableMSR.Recovery.WindowCSP.bounded_width_window_search_program
   https://prove2.me/theorems/305b164a-bfc8-43ef-9d64-99d7435efca8
   Accepted sketch 6cda1f4c-9f6c-4677-82a0-f3b58034300f. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage5
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
open Polynomial
private noncomputable def boundPoly : Polynomial ℕ := X+C 4*(1+X^4)+1
private lemma capUp (x : World) (m : Mem) : (arena x m).cap≤ boundPoly.eval x.cap:=by
  have ns : x.n≤ x.cap:=by dsimp [World.cap];omega
  have rs : x.rows≤ x.cap:=by dsimp [World.cap];omega
  have prod:=Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul rs ns) ns) ns
  have plus : x.n+x.k+1≤ x.cap:=by dsimp [World.cap];omega
  change x.n+x.k+height x+1≤_
  simp only [boundPoly,eval_add,eval_mul,eval_one,eval_X,eval_C,eval_pow]
  rw [show x.cap^4=x.cap*x.cap*x.cap*x.cap by ring]
  unfold height capacity;omega
private lemma monoEval (p : Polynomial ℕ) {i j : ℕ} (h : i≤ j) : p.eval i≤ p.eval j:=by
  rw [Polynomial.eval_eq_sum_range,Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun k _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h k))
private lemma capPoly (p : Polynomial ℕ) : ∃c D : ℕ,∀m : ℕ,1≤ m → p.eval m≤ c*m^D := by
  classical
  let D:=p.natDegree+1
  refine ⟨∑i ∈ Finset.range D,p.coeff i,D,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  apply Finset.sum_le_sum;intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Finset.mem_range.mp hi).le)
theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,searchSpec e c D b cmd := by
  obtain ⟨c,D,b,hc,hb,make⟩:=(StableMSRCompiledRecoveryStage4.fromDense dense)
  obtain ⟨P,packC,packRun⟩:=native_count_graph
  obtain ⟨Q,solve,solveRun⟩:=RegionalBallDP.decode_regional_menus
  let A:=P+Q.comp boundPoly+boundPoly
  obtain ⟨C,T,major⟩:=capPoly A
  refine ⟨c+C+1,D+T,b,by omega,hb,?_⟩
  intro e epos el
  obtain ⟨makeC,makeRun⟩:=make e epos el
  refine ⟨makeC.seq (packC.seq solve),?_⟩
  intro x s hk kn metric ready
  obtain ⟨a,l,ea,al,ar,profile⟩:=makeRun x s hk kn metric ready
  let y:=worldOf x.k x.rows x.dist a
  obtain ⟨v,j,ev,jp,vr,grid⟩:=packRun y a hk kn ar
  let m : Mem:=fun i=>v.imem (i:ℤ)
  let g:=arena y m
  obtain ⟨t,z,et,zq,tReady,ends,best⟩:=solveRun g v hk (by change 0< x.n;omega) grid.sized vr
  let N:=x.n^(b*parameterEnvelope (e:ℝ))
  let V:=x.cap
  have non : 1≤ V:=by dsimp [V,World.cap];omega
  have npos : 1≤ N:=Nat.one_le_pow _ _ (by omega)
  have gup : g.cap≤ boundPoly.eval V:=capUp y m
  have K:=major V non
  change (P+Q.comp boundPoly+boundPoly).eval V≤ C*V^T at K
  simp only [eval_add,eval_comp] at K
  have jq : j≤ P.eval V:=jp
  have zq' :=zq.trans (monoEval Q gup)
  have heightB : height y≤ boundPoly.eval V:=by
    apply le_trans _ gup;change height y≤ y.n+y.k+height y+1;omega
  have small (a : ℕ) (h : a≤ T+D) : V^a≤ V^(D+T):=Nat.pow_le_pow_right non (by omega)
  have additive : j+z≤ C*V^(D+T)*N:=calc
    j+z≤ C*V^T :=by omega
    _≤ C*V^(D+T)*N :=by
      apply le_trans (Nat.mul_le_mul_left _ (small T (by omega)))
      exact Nat.le_mul_of_pos_right _ npos
  have localBound : l≤ c*V^(D+T)*N:=al.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (small D (by omega))))
  have upper : c*V^(D+T)*N+C*V^(D+T)*N≤(c+C+1)*V^(D+T)*N:=by
    rw [←Nat.add_mul,←Nat.add_mul];exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have heightC : height y≤ C*V^(D+T)*N:=calc
    height y≤ C*V^T:=by omega
    _≤ C*V^(D+T)*N:=(Nat.mul_le_mul_left _ (small T (by omega))).trans (Nat.le_mul_of_pos_right _ npos)
  refine ⟨t,_,height y,.seq ea (.seq ev et),by change l+(j+z)≤(c+C+1)*V^(D+T)*N;omega,by change height y≤(c+C+1)*V^(D+T)*N;omega,tReady,ends,?_⟩
  intro u hu pos tw P' validP total
  obtain ⟨vert,table,w,path,cheap⟩:=local_profiles_certify_exact_count_search x e y.mem m (by omega) profile grid u hu pos tw P' validP total
  obtain ⟨good,cost⟩:=best _ vert table w path
  exact ⟨_,table.1,good,cost.trans cheap⟩
end StableMSRCompiledRecoveryStage5

/- Original mission reduction: StableMSR.Recovery.RegionalBallDP.dense_local_region_menu_generator
   https://prove2.me/theorems/d7b21840-6701-4f78-8793-1f21b839dfa8
   Accepted sketch aa5db9f6-00b6-4935-b078-56ac40122e6e. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage6
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
open StableMSR.Recovery.RegionalBallDP
open Polynomial
private lemma capPoly (p : Polynomial ℕ) : ∃c D : ℕ,∀m : ℕ,1≤ m → p.eval m≤ c*m^D := by
  classical
  let D:=p.natDegree+1
  refine ⟨∑i ∈ Finset.range D,p.coeff i,D,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range,Finset.sum_mul]
  apply Finset.sum_le_sum;intro i hi
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Finset.mem_range.mp hi).le)
private lemma absorb (a b c D f n k H E z l : ℕ) (hn : 1≤ n) (hk : k≤ n) (hb : 1≤ b) (he : 1≤ E)
    (hz : z≤ a*n^(b*E)) (hH : H≤ a*n^(b*E)) (hl : l≤ c*(n+k+H+1)^D*n^(f*E)) :
    z+l≤(a+c*(a+3)^D)*n^((b*(D+1)+f)*E) := by
  let K:=n^(b*E)
  have one : 1≤ K:=Nat.one_le_pow _ _ hn
  have small : n≤ K := by simpa [K] using Nat.pow_le_pow_right hn (show 1≤ b*E by exact Nat.mul_pos hb he)
  change H≤ a*K at hH
  have cap : n+k+H+1≤(a+3)*K := by rw [Nat.add_mul];omega
  have l' := hl.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c (Nat.pow_le_pow_left cap D)))
  rw [Nat.mul_pow] at l'
  have bp : b≤ b*(D+1)+f := by rw [Nat.mul_add];omega
  have dp : b*D+f≤ b*(D+1)+f := by rw [Nat.mul_add];omega
  have base := Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E bp)
  have high := Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E dp)
  have prod : K^D*n^(f*E)=n^((b*D+f)*E) := by
    dsimp [K];rw [←Nat.pow_mul,←Nat.pow_add];congr 1;ring
  rw [Nat.add_mul]
  apply Nat.add_le_add (hz.trans (Nat.mul_le_mul_left a base))
  calc
    l ≤ c*((a+3)^D*K^D)*n^(f*E) := l'
    _ = (c*(a+3)^D)*(K^D*n^(f*E)) := by ring
    _ ≤ _ := by rw [prod];exact Nat.mul_le_mul_left _ high
theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃a b : ℕ,0< a ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 →
    ∃cmd : Cmd,∀(n k : ℕ) (d : Point n→Point n→ℝ),
      1≤ k → k< n → fewBound (e:ℝ)< k → IsMetricArray d → localSpec e a b cmd n k d := by
  obtain ⟨a,b,apos,bpos,start⟩:=dense_aligned_scenario_program
  obtain ⟨c,D,f,_,_,search⟩:=(StableMSRCompiledRecoveryStage5.fromDense dense)
  obtain ⟨p,wrap,encode⟩:=catalog_to_local_trials
  obtain ⟨c₂,D₂,ce⟩:=capPoly (p+C 4*X+C 5)
  let A:=a+c*(a+3)^D
  let B:=b*(D+1)+f
  have positive : 0< B:= by dsimp [B];positivity
  refine ⟨A+c₂*(A+3)^D₂,B*(D₂+1)+0,by dsimp [A];omega,by positivity,?_⟩
  intro e he hl
  obtain ⟨prep,hPrep⟩:=start e he hl
  obtain ⟨post,hPost⟩:=search e he hl
  refine ⟨.seq prep (.seq post wrap),?_⟩
  intro n k d hk kn big met
  obtain ⟨s,z,H,ez,tz,hH,rs,scene⟩:=hPrep n k d hk kn big met
  let x:=worldOf k H d s
  obtain ⟨m,l,J,el,tl,hJ,rm,ends,answer⟩:=hPost x s hk kn met rs
  let y:=worldOf k J d m
  obtain ⟨t,u,eu,tu,rt,shape',trial⟩:=encode y m hk rm ends
  let E:=parameterEnvelope (e:ℝ)
  have epos : 1≤ E:=by dsimp [E,parameterEnvelope];omega
  have first := absorb a b c D f n k H E z l (by omega) kn.le bpos epos tz hH tl
  have size₁ := absorb a b c D f n k H E 0 J (by omega) kn.le bpos epos (by omega) hH hJ
  change z+l≤ A*n^(B*E) at first
  change 0+J≤ A*n^(B*E) at size₁
  simp only [Nat.zero_add] at size₁
  have cap:=ce y.cap (by unfold World.cap;omega)
  simp only [eval_add,eval_mul,eval_X,eval_C] at cap
  have ul : u≤ c₂*(n+k+J+1)^D₂*n^(0*E) := by simp;change u≤ c₂*y.cap^D₂;omega
  have hj : 1+4*(J+1)≤ c₂*(n+k+J+1)^D₂*n^(0*E) := by
    simp;change 1+4*(J+1)≤ c₂*y.cap^D₂
    have le : J≤ y.cap:=by dsimp [World.cap,y,worldOf];omega
    omega
  have second:=absorb A B c₂ D₂ 0 n k J E (z+l) u (by omega) kn.le positive epos first size₁ ul
  have last:=absorb A B c₂ D₂ 0 n k J E 0 (1+4*(J+1)) (by omega) kn.le positive epos (by omega) size₁ hj
  refine ⟨t,_,1+4*(J+1),.seq ez (.seq el eu),?_,by simpa only [Nat.zero_add] using last,rt,shape',?_⟩
  · simpa only [Nat.add_assoc] using second
  · intro O stable many
    obtain ⟨a,ah,ap,ae,ad⟩:=scene O stable many
    obtain ⟨widths,P,hp,num,cost'⟩:=aligned_scenario_has_exact_assignment x a (e:ℝ)
      (by exact_mod_cast he) (by exact_mod_cast hl) hk kn met O stable ap ae ad
    obtain ⟨r,hr,good',le⟩:=answer a ah ap widths P hp num
    exact ⟨r+2,trial r hr good' (cost d O) (le.trans cost'.le)⟩
end StableMSRCompiledRecoveryStage6

/- Original mission reduction: StableMSR.Recovery.RegionalBallDP.dense_factorized_regional_catalog
   https://prove2.me/theorems/e01917ae-33d7-4be0-917b-2d9e081b1707
   Accepted sketch 39ddf0f3-9ac1-44ab-805d-4098c9e85d52. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage7
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃a b : ℕ,0<a ∧ 0<b ∧ ∀e : ℚ,0<e → e<1 →
    ∃cmd : Cmd,∀(n k : ℕ) (d : Point n→Point n→ℝ),
      1≤k → k<n → fewBound (e:ℝ)<k → IsMetricArray d → regionalSpec e a b cmd n k d := by
  obtain ⟨a,b,ha,hb,gen⟩:=(StableMSRCompiledRecoveryStage6.fromDense dense)
  refine ⟨a,b,ha,hb,?_⟩
  intro e he he'
  obtain ⟨cmd,run⟩:=gen e he he'
  refine ⟨cmd,?_⟩
  intro n k d hk kn big metric
  obtain ⟨s,z,H,ez,tz,hH,ready,hs,ok⟩:=run n k d hk kn big metric
  refine ⟨s,z,H,ez,tz,hH,ready,hs,?_⟩
  intro O stable many
  obtain ⟨v,⟨trial⟩⟩:=ok O stable many
  exact ⟨v,disjoint_local_menus_certify_terminal _ hs v _ trial⟩
end StableMSRCompiledRecoveryStage7

/- Original mission reduction: StableMSR.Recovery.FewBallRows.dense_ball_cover_catalog
   https://prove2.me/theorems/a8f25099-08ee-4f83-a488-da4e074dd8b8
   Accepted sketch f116206f-e457-4c41-81ee-42be6c2d9962. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage8
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
private lemma capPoly (p : Polynomial ℕ) :
    ∃c D : ℕ,∀m : ℕ,1 ≤ m → p.eval m ≤ c*m^D := by
  classical
  let e := p.natDegree+1
  let s := ∑ i ∈ Finset.range e,p.coeff i
  refine ⟨s,e,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑i ∈ Finset.range e,p.coeff i*m^e := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Nat.le_of_lt (Finset.mem_range.mp hi)))
    _ = s*m^e := (Finset.sum_mul ..).symm
private lemma combineTime (a b c D n k H E z l : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hb : 1 ≤ b) (he : 1 ≤ E) (hz : z ≤ a*n^(b*E)) (hh : H ≤ a*n^(b*E))
    (hl : l ≤ c*(n+k+H+1)^D) :
    z+l+1 ≤ (a+c*(a+3)^D+1)*n^((b*(D+1))*E) := by
  let B := n^(b*E)
  have hB : 1 ≤ B := Nat.one_le_pow _ _ hn
  have bn : n ≤ B := by
    change n ≤ n^(b*E)
    have t := Nat.pow_le_pow_right hn (show 1 ≤ b*E by exact Nat.mul_pos hb he)
    simpa using t
  change H ≤ a*B at hh
  change z ≤ a*B at hz
  have cap : n+k+H+1 ≤ (a+3)*B := by rw [Nat.add_mul];omega
  have bound := hl.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left cap D))
  rw [Nat.mul_pow] at bound
  have bd : B^D ≤ B^(D+1) := Nat.pow_le_pow_right hB (by omega)
  have bb : B ≤ B^(D+1) := by
    simpa using Nat.pow_le_pow_right hB (show 1 ≤ D+1 by omega)
  have one : 1 ≤ B^(D+1) := Nat.one_le_pow _ _ hB
  rw [show (b*(D+1))*E=(b*E)*(D+1) by ring,Nat.pow_mul]
  change z+l+1 ≤ (a+c*(a+3)^D+1)*B^(D+1)
  rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
  apply Nat.add_le_add _ one
  apply Nat.add_le_add (hz.trans (Nat.mul_le_mul_left a bb))
  rw [← Nat.mul_assoc] at bound
  exact bound.trans (Nat.mul_le_mul_left _ bd)

theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃a b : ℕ,0 < a ∧ 0 < b ∧ ∀e : ℚ,0 < e → e < 1 →
    ∃cmd : Cmd,∀ (n k : ℕ) (d : Point n→Point n→ℝ),
      1 ≤ k → k < n → fewBound (e:ℝ) < k → IsMetricArray d → denseSpec e a b cmd n k d := by
  obtain ⟨a,b,ha,hb,gen⟩:=(StableMSRCompiledRecoveryStage7.fromDense dense)
  obtain ⟨p,post,runPost⟩:=decode_regional_menus
  obtain ⟨c,D,cp⟩:=capPoly p
  refine ⟨a+c*(a+3)^D+1,b*(D+1),by omega,Nat.mul_pos hb (by omega),?_⟩
  intro e he he'
  obtain ⟨cmd,run⟩:=gen e he he'
  refine ⟨.seq cmd post,?_⟩
  intro n k d hk hn hlarge metric
  obtain ⟨s,z,H,ez,tz,hH,rs,shape',localOpt⟩:=run n k d hk hn hlarge metric
  let x:=worldOf k H d s
  obtain ⟨t,l,el,tl,rt,ep,decode⟩:=runPost x s hk (by change 0<n;omega) shape' rs
  have budget:=combineTime a b c D n k H (parameterEnvelope (e:ℝ)) z l (by omega) hn.le hb
    (by unfold parameterEnvelope;omega) tz hH (tl.trans (cp x.cap (by unfold World.cap;omega)))
  have total : a*n^(b*parameterEnvelope (e:ℝ))≤(a+c*(a+3)^D+1)*n^((b*(D+1))*parameterEnvelope (e:ℝ)) := by
    apply Nat.mul_le_mul (by omega)
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right b (by omega))
  refine ⟨t,_,H,.seq ez el,by omega,hH.trans total,rt,ep,?_⟩
  intro O stable many
  obtain ⟨v,hv,cert,u,path,bound⟩:=localOpt O stable many
  obtain ⟨good',le⟩:=decode v hv cert u path
  exact ⟨v,cert.1,good',le.trans bound⟩
end StableMSRCompiledRecoveryStage8

/- Original mission reduction: StableMSR.Recovery.CartesianBallRows.interior_ball_cover_catalog
   https://prove2.me/theorems/d84b36c0-8e45-4273-8b01-216fdb0179f5
   Accepted sketch 9b764216-9098-496a-8956-1ac1f442f5a0. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage9
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private lemma capPoly (p : Polynomial ℕ) :
    ∃c D : ℕ,∀m : ℕ,1 ≤ m → p.eval m ≤ c*m^D := by
  classical
  let e := p.natDegree+1
  let s := ∑ i ∈ Finset.range e,p.coeff i
  refine ⟨s,e,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑i ∈ Finset.range e,p.coeff i*m^e := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Nat.le_of_lt (Finset.mem_range.mp hi)))
    _ = s*m^e := (Finset.sum_mul ..).symm
private lemma combineTime (a b c D n k H E z l : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hb : 1 ≤ b) (he : 1 ≤ E) (hz : z ≤ a*n^(b*E)) (hh : H ≤ a*n^(b*E))
    (hl : l ≤ c*(n+k+H+1)^D) :
    z+l+1 ≤ (a+c*(a+3)^D+1)*n^((b*(D+1))*E) := by
  let B := n^(b*E)
  have hB : 1 ≤ B := Nat.one_le_pow _ _ hn
  have bn : n ≤ B := by
    change n ≤ n^(b*E)
    have t := Nat.pow_le_pow_right hn (show 1 ≤ b*E by exact Nat.mul_pos hb he)
    simpa using t
  change H ≤ a*B at hh
  change z ≤ a*B at hz
  have cap : n+k+H+1 ≤ (a+3)*B := by rw [Nat.add_mul];omega
  have bound := hl.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left cap D))
  rw [Nat.mul_pow] at bound
  have bd : B^D ≤ B^(D+1) := Nat.pow_le_pow_right hB (by omega)
  have bb : B ≤ B^(D+1) := by
    simpa using Nat.pow_le_pow_right hB (show 1 ≤ D+1 by omega)
  have one : 1 ≤ B^(D+1) := Nat.one_le_pow _ _ hB
  rw [show (b*(D+1))*E=(b*E)*(D+1) by ring,Nat.pow_mul]
  change z+l+1 ≤ (a+c*(a+3)^D+1)*B^(D+1)
  rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
  apply Nat.add_le_add _ one
  apply Nat.add_le_add (hz.trans (Nat.mul_le_mul_left a bb))
  rw [← Nat.mul_assoc] at bound
  exact bound.trans (Nat.mul_le_mul_left _ bd)

theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃a b : ℕ,0 < a ∧ 0 < b ∧ ∀e : ℚ,0 < e → e < 1 →
    ∃cmd : Cmd,∀ (n k : ℕ) (d : Point n→Point n→ℝ),
      1 ≤ k → k < n → fewBound (e:ℝ) < k → IsMetricArray d → runSpec e a b cmd n k d := by
  classical
  obtain ⟨a,b,ha,hb,dense⟩ := (StableMSRCompiledRecoveryStage8.fromDense dense)
  obtain ⟨p,appendRows⟩ := append_few_large_recovery
  obtain ⟨c,D,poly⟩ := capPoly p
  let A := a+1
  let B := b+2
  refine ⟨A+c*(A+3)^D+1,B*(D+1),by omega,Nat.mul_pos (by dsimp [B];omega) (by omega),?_⟩
  intro e he hlt
  let h := fewBound (e:ℝ)
  let E := parameterEnvelope (e:ℝ)
  obtain ⟨G,gen⟩ := dense e he hlt
  obtain ⟨J,joinRows⟩ := appendRows h
  refine ⟨.seq G J,?_⟩
  intro n k d hk kn largeK metric
  obtain ⟨s,z,H,ez,tz,th,rd,ends,covers⟩ := gen n k d hk kn largeK metric
  let x := worldOf k H d s
  let F := rows n (h+1)
  obtain ⟨t,l,el,tl,ready,valid,old,new'⟩ := joinRows x s hk kn largeK metric rd
  have hn : 1≤n := by omega
  have wE : h+1≤E := by dsimp [h,E,parameterEnvelope];omega
  have hp : 1≤E := by omega
  have shift : n^(b*E) ≤ n^(B*E) := Nat.pow_le_pow_right hn (Nat.mul_le_mul_right _ (by dsimp [B];omega))
  have up := Nat.mul_le_mul_left a shift
  have ff : F≤n^(B*E) := Nat.pow_le_pow_right hn (Nat.mul_le_mul (by dsimp [B];omega : 2≤B) wE)
  have H' : H+F≤A*n^(B*E) := by
    change H≤a*n^(b*E) at th
    dsimp [A];rw [Nat.add_mul,Nat.one_mul];omega
  have zz : z≤A*n^(B*E) := by
    change z≤a*n^(b*E) at tz
    dsimp [A];rw [Nat.add_mul,Nat.one_mul];omega
  have cap : x.cap+rows x.n (h+1)=n+k+(H+F)+1 := by dsimp [x,worldOf,World.cap,F];omega
  have smallTime := tl.trans (poly _ (by rw [cap];omega))
  rw [cap] at smallTime
  have total := combineTime A B c D n k (H+F) E z l hn kn.le (by dsimp [B];omega) hp zz H' smallTime
  have exponent : B*E≤(B*(D+1))*E := Nat.mul_le_mul_right _ (by nlinarith [Nat.zero_le (B*D)])
  have tableTime := H'.trans (Nat.mul_le_mul (show A≤A+c*(A+3)^D+1 by omega) (Nat.pow_le_pow_right hn exponent))
  refine ⟨t,_,H+F,Executes.seq ez el,(Nat.le_succ (z+l)).trans total,tableTime,ready,valid ends,?_⟩
  intro O stable
  by_cases few : (largeClusters d O (e:ℝ)).card≤h
  · obtain ⟨u,hu,g,price⟩ := new' (e:ℝ) (by exact_mod_cast he) (by exact_mod_cast hlt) O stable few
    exact ⟨H+u,Nat.add_lt_add_left hu _,g,price.le⟩
  · obtain ⟨r,hr,g,price⟩ := covers O stable (lt_of_not_ge few)
    obtain ⟨good',eq⟩ := old r hr g
    exact ⟨r,by omega,good',eq.le.trans price⟩
end StableMSRCompiledRecoveryStage9

/- Original mission reduction: StableMSR.Recovery.BallCoverCatalog.uniform_ball_cover_catalog
   https://prove2.me/theorems/b52c1366-e0b0-43a1-9fba-a4a752b87f21
   Accepted sketch 89b95ff7-dbdf-4eb2-9093-32d79144cfb2. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage10
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial
open StableMSR.Recovery.BallCoverCatalog
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
open StableMSR.Recovery.CartesianBallRows
private def setup (B : ℕ) := Cmd.seq (.atom (.integerLoad 0 2)) (.seq (.atom (.pointerConst 1 1))
  (.seq (.atom (.integerLoad 1 1)) (.atom (.pointerConst 2 B))))
private def reset := Cmd.seq (.atom (.pointerConst 0 0)) (.seq (.atom (.pointerConst 1 0)) (.atom (.pointerConst 2 0)))
private lemma prepare {n : ℕ} (d : Point n→Point n→ℝ) (k B : ℕ) :
    ∃s,Executes d (setup B) (initialStore n k) s 4 ∧ s.ptrs 0=(n:ℤ) ∧
      s.ptrs 1=(k:ℤ) ∧ s.ptrs 2=(B:ℤ) ∧ Executes d reset s (initialStore n k) 3 := by
  let s := (Op.pointerConst 2 B).eval d ((Op.integerLoad 1 1).eval d ((Op.pointerConst 1 1).eval d
    ((Op.integerLoad 0 2).eval d (initialStore n k))))
  let t := (Op.pointerConst 2 0).eval d ((Op.pointerConst 1 0).eval d ((Op.pointerConst 0 0).eval d s))
  have endState : t=initialStore n k := by
    dsimp [t,s,Op.eval,initialStore]
    congr 1
    funext j
    by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> by_cases h2 : j=2 <;> simp [Function.update,h0,h1,h2]
  refine ⟨s,.seq (.atom _ _) (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))),?_,?_,?_,?_⟩
  all_goals try solve | simp [s,Op.eval,initialStore,Function.update]
  rw [← endState]
  exact .seq (.atom _ _) (.seq (.atom _ _) (.atom _ _))

theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) : ∃a b : ℕ,0 < a ∧ 0 < b ∧
    ∀e : ℚ,0 < e → e < 1 → ∃cmd : Cmd,HasCatalog e a b cmd := by
  obtain ⟨a,b,ha,hb,hard⟩ := (StableMSRCompiledRecoveryStage9.fromDense dense)
  obtain ⟨c,v,hc,hv,S,small⟩ := cartesian_row_machine
  obtain ⟨l,hl,D,diag⟩ := singleton_cover_machine
  let A := a+c+l
  let B := b+v+2
  refine ⟨A+20,B,by omega,by dsimp [B];omega,?_⟩
  intro e he he'
  obtain ⟨G,hG⟩ := hard e he he'
  let N := fewBound (e:ℝ)
  let E := parameterEnvelope (e:ℝ)
  let first := Cond.pointerLE 0 1
  let second := Cond.pointerLE 1 2
  let wrap := fun cmd=>Cmd.seq reset cmd
  refine ⟨.seq (setup N) (.ite first (wrap D) (.ite second (wrap S) (wrap G))),?_⟩
  intro n k d hk hn hm
  have npos : 0 < n := by omega
  have epos : 1 ≤ E := by unfold E parameterEnvelope;omega
  let K := n^(B*E)
  have kpos : 1 ≤ K := Nat.one_le_pow _ _ npos
  have nK : n ≤ K := by
    simpa using Nat.pow_le_pow_right npos (show 1 ≤ B*E from Nat.mul_pos (by dsimp [B];omega) epos)
  have reserve : A*K+11 ≤ (A+20)*K := by rw [Nat.add_mul A 20 K];omega
  have padding : A*K ≤ (A+20)*K := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨s,setupEx,p0,p1,p2,restore⟩ := prepare d k N
  by_cases eq : n=k
  · subst k
    obtain ⟨t,z,ez,tz,rd,ep,gu⟩ := diag n d npos hm
    have cond : first.test s := by change s.ptrs 0 ≤ s.ptrs 1;rw [p0,p1]
    have tt : z ≤ A*K := tz.trans (Nat.mul_le_mul (by dsimp [A];omega) nK)
    refine ⟨t,_,1,.seq setupEx (.ite_true cond (.seq restore ez)),?_,?_,rd,ep,?_⟩
    · apply le_trans _ reserve;omega
    · apply le_trans kpos;change K ≤ (A+20)*K;rw [Nat.add_mul];omega
    · intro O hO;exact gu O hO.1
  · have less : k < n := by omega
    have nfirst : ¬first.test s := by change ¬s.ptrs 0 ≤ s.ptrs 1;rw [p0,p1];omega
    by_cases ks : k ≤ N
    · obtain ⟨t,z,ez,tz,rd,pp⟩ := small n k d hk hn
      have cond : second.test s := by change s.ptrs 1 ≤ s.ptrs 2;rw [p1,p2];exact_mod_cast ks
      have kE : k+1 ≤ E := by unfold E parameterEnvelope;change k ≤ fewBound _ at ks;omega
      have bv : v ≤ B := by dsimp [B];omega
      have tt : z ≤ A*K := tz.trans (Nat.mul_le_mul (by dsimp [A];omega)
        (Nat.pow_le_pow_right npos (Nat.mul_le_mul bv kE)))
      have H : rows n k ≤ K := Nat.pow_le_pow_right npos (Nat.mul_le_mul (show 2 ≤ B by dsimp [B];omega) (by omega))
      obtain ⟨ends,cover⟩ := cartesian_rows_certify_partitions _ npos pp
      refine ⟨t,_,rows n k,.seq setupEx (.ite_false nfirst (.ite_true cond (.seq restore ez))),?_,?_,rd,ends,?_⟩
      · apply le_trans _ reserve;omega
      · apply H.trans;change K ≤ (A+20)*K;rw [Nat.add_mul];omega
      · intro O ho;obtain ⟨r,hr,g,eq⟩ := cover O ho.1;exact ⟨r,hr,g,eq.le⟩
    · obtain ⟨t,z,H,ez,tz,rr,rd,ep,gu⟩ := hG n k d hk less (by exact lt_of_not_ge ks) hm
      have cond : ¬second.test s := by change ¬s.ptrs 1 ≤ s.ptrs 2;rw [p1,p2];omega
      have mag : a*n^(b*parameterEnvelope (e:ℝ)) ≤ A*K := Nat.mul_le_mul (by dsimp [A];omega)
        (Nat.pow_le_pow_right npos (Nat.mul_le_mul_right E (by dsimp [B];omega)))
      refine ⟨t,_,H,.seq setupEx (.ite_false nfirst (.ite_false cond (.seq restore ez))),?_,?_,rd,ep,gu⟩
      · apply le_trans _ reserve;have := tz.trans mag;omega
      · exact (rr.trans mag).trans padding
end StableMSRCompiledRecoveryStage10

/- Original mission reduction: StableMSR.Recovery.rational_recovery_program
   https://prove2.me/theorems/c2468a82-f9f1-431f-bb25-e0e414912c4f
   Accepted sketch eabd27a5-d2f7-407b-8bc8-0847e076c8d9. The dense-circuit hypothesis is explicit here. -/
namespace StableMSRCompiledRecoveryStage11
set_option autoImplicit false
open scoped Classical
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
private lemma capPoly (p : Polynomial ℕ) :
    ∃c D : ℕ,∀m : ℕ,1 ≤ m → p.eval m ≤ c*m^D := by
  classical
  let e := p.natDegree+1
  let s := ∑ i ∈ Finset.range e,p.coeff i
  refine ⟨s,e,?_⟩
  intro m hm
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ ∑i ∈ Finset.range e,p.coeff i*m^e := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hm (Nat.le_of_lt (Finset.mem_range.mp hi)))
    _ = s*m^e := (Finset.sum_mul ..).symm
private lemma combineTime (a b c D n k H E z l : ℕ) (hn : 1 ≤ n) (hk : k ≤ n)
    (hb : 1 ≤ b) (he : 1 ≤ E) (hz : z ≤ a*n^(b*E)) (hh : H ≤ a*n^(b*E))
    (hl : l ≤ c*(n+k+H+1)^D) :
    z+l+1 ≤ (a+c*(a+3)^D+1)*n^((b*(D+1))*E) := by
  let B := n^(b*E)
  have hB : 1 ≤ B := Nat.one_le_pow _ _ hn
  have bn : n ≤ B := by
    change n ≤ n^(b*E)
    have t := Nat.pow_le_pow_right hn (show 1 ≤ b*E by exact Nat.mul_pos hb he)
    simpa using t
  change H ≤ a*B at hh
  change z ≤ a*B at hz
  have cap : n+k+H+1 ≤ (a+3)*B := by rw [Nat.add_mul];omega
  have bound := hl.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left cap D))
  rw [Nat.mul_pow] at bound
  have bd : B^D ≤ B^(D+1) := Nat.pow_le_pow_right hB (by omega)
  have bb : B ≤ B^(D+1) := by
    simpa using Nat.pow_le_pow_right hB (show 1 ≤ D+1 by omega)
  have one : 1 ≤ B^(D+1) := Nat.one_le_pow _ _ hB
  rw [show (b*(D+1))*E=(b*E)*(D+1) by ring,Nat.pow_mul]
  change z+l+1 ≤ (a+c*(a+3)^D+1)*B^(D+1)
  rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
  apply Nat.add_le_add _ one
  apply Nat.add_le_add (hz.trans (Nat.mul_le_mul_left a bb))
  rw [← Nat.mul_assoc] at bound
  exact bound.trans (Nat.mul_le_mul_left _ bd)

theorem fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      ∀ ε₀ : ℚ, 0 < ε₀ → ε₀ < 1 →
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            ∃ t ≤ a * n ^ (b * parameterEnvelope (ε₀ : ℝ)),
              let s := execute P n k d t
              s.halted = true ∧
                s.work ≤ a * n ^ (b * parameterEnvelope (ε₀ : ℝ)) ∧
                ValidLabels n k s ∧
                ∀ O, Stable d k (1 + (ε₀ : ℝ)) O → outputPartition n k s = O := by
  obtain ⟨a,b,ha,hb,hgen⟩ := (StableMSRCompiledRecoveryStage10.fromDense dense)
  obtain ⟨p,w,writer⟩ := point_output_loop output selector_expression
  obtain ⟨c,D,bound⟩ := capPoly p
  refine ⟨a+c*(a+3)^D+1,b*(D+1),by omega,Nat.mul_pos hb (by omega),?_⟩
  intro e he he'
  obtain ⟨gen,hg⟩ := hgen e he he'
  let cmd := Cmd.seq gen w
  obtain ⟨safe,corr⟩ := compiler_execution_exact cmd 0
  refine ⟨compile cmd 0,safe,?_⟩
  intro n k d hk hn hm
  obtain ⟨s,z,H,ez,tz,hH,rd,ends,wit⟩ := hg n k d hk hn hm
  let x := worldOf k H d s
  obtain ⟨v,l,el,tl,labels⟩ := writer x s rd
  have exe : Executes d cmd (initialStore n k) v (z+l) := .seq ez el
  have init : MinSumFPT.initState n k 0 0=(initialStore n k).state 0 0 := by simp [initialStore,Store.state,MinSumFPT.initState]
  have final : execute (compile cmd 0) n k d (z+l+1)=v.haltedState cmd.size (0+(z+l)+1) 0 := by
    unfold execute MinSumFPT.run
    rw [init]
    exact corr n d _ v _ exe (fun _=>0) 0
  have hbnd := tl.trans (bound x.cap (by unfold World.cap;omega))
  have et : 1 ≤ parameterEnvelope (e:ℝ) := by unfold parameterEnvelope;omega
  have total := combineTime a b c D n k H _ z l (by omega) hn hb et tz hH hbnd
  have lab : ∀i < x.n,(v.haltedState cmd.size (0+(z+l)+1) 0).imem (-1-(i:ℤ))=output x i := labels
  obtain ⟨valid,recov⟩ := cheapest_cover_recovers x _ hk hn hm ends lab
  refine ⟨z+l+1,total,?_⟩
  dsimp only
  rw [final]
  refine ⟨rfl,by simpa [Store.haltedState,Store.state] using total,valid,?_⟩
  intro O ho
  have ep : (0:ℝ) < (e:ℝ) := by exact_mod_cast he
  exact recov (1+(e:ℝ)) (by linarith) O ho (wit O ho)
end StableMSRCompiledRecoveryStage11

/- Original mission reduction: StableMSR.Recovery.deterministic_exact_recovery
   https://prove2.me/theorems/6a8c0ab2-0fdc-46c1-beac-599a693f15ee
   Accepted sketch 3f27d934-a459-4c23-8273-dbd6fb426c19. The dense-circuit hypothesis is explicit here. -/
section FinalCalibration
set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery
namespace CalibrationAux

/-- A fixed rational stability margin can be selected before the input instance. -/
lemma exists_rational_calibration (γ : ℝ) (hγ : 1 < γ) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
      (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
       else ε₀ = 1 / 2) ∧ 1 + (ε₀ : ℝ) < γ := by
  by_cases hsmall : γ < 2
  · obtain ⟨ε₀, hlo, hhi⟩ :=
      exists_rat_btwn (show (γ - 1) / 2 < γ - 1 by linarith)
    have hpos : (0 : ℝ) < (ε₀ : ℝ) := by linarith
    have hone : (ε₀ : ℝ) < 1 := by linarith
    refine ⟨ε₀, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hpos
    · exact_mod_cast hone
    · simpa only [if_pos hsmall] using And.intro hlo.le hhi
    · linarith
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_, ?_⟩
    · simp only [if_neg hsmall]
    · push_cast
      linarith

/-- A fifth-power envelope survives the rational calibration, with an absolute factor 32. -/
lemma exists_calibration_with_envelope (K : ℝ) (hK : 0 < K)
    (hE : ∀ ε : ℝ, 0 < ε → ε < 1 →
      (parameterEnvelope ε : ℝ) ≤ K / ε ^ 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, 1 < γ →
      ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        (γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5) ∧
        1 + (ε₀ : ℝ) < γ := by
  refine ⟨32 * K, by positivity, ?_⟩
  intro γ hγ
  obtain ⟨ε₀, hpos, hone, hrange, hmargin⟩ := exists_rational_calibration γ hγ
  refine ⟨ε₀, hpos, hone, hrange, ?_, hmargin⟩
  intro hsmall
  have hepos : (0 : ℝ) < (ε₀ : ℝ) := by exact_mod_cast hpos
  have heone : (ε₀ : ℝ) < 1 := by exact_mod_cast hone
  have hlo : (γ - 1) / 2 ≤ (ε₀ : ℝ) :=
    (by simpa only [if_pos hsmall] using hrange :
      (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1).1
  have hδ : 0 < γ - 1 := by linarith
  have hp : (γ - 1) ^ 5 ≤ (2 * (ε₀ : ℝ)) ^ 5 :=
    pow_le_pow_left₀ hδ.le (by linarith) 5
  rw [mul_pow] at hp
  norm_num at hp
  calc
    (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ K / (ε₀ : ℝ) ^ 5 := hE _ hepos heone
    _ ≤ (32 * K) / (γ - 1) ^ 5 := by
      apply (div_le_div_iff₀ (pow_pos hepos 5) (pow_pos hδ 5)).2
      nlinarith [mul_le_mul_of_nonneg_left hp hK.le]

/-- Enlarging the perturbation factor preserves membership in the perturbation family. -/
lemma perturbation_mono {n : ℕ} {d d' : Point n → Point n → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) {α β : ℝ} (hαβ : α ≤ β)
    (hp : Perturbation d α d') : Perturbation d β d' := by
  refine ⟨hp.1, ?_⟩
  intro x y
  exact ⟨(hp.2 x y).1,
    (hp.2 x y).2.trans (mul_le_mul_of_nonneg_right hαβ (hd x y))⟩

/-- Stability at a larger factor implies stability at every smaller factor. -/
lemma stable_mono {n k : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {α β : ℝ} (hαβ : α ≤ β)
    {O : Partition n} (hO : Stable d k β O) : Stable d k α O := by
  rcases hd with ⟨m, hm⟩
  letI : MetricSpace (Point n) := m
  have hn : ∀ x y, 0 ≤ d x y := by
    intro x y
    rw [← hm x y]
    exact dist_nonneg
  exact ⟨hO.1, fun d' hp => hO.2 d' (perturbation_mono hn hαβ hp)⟩

/-- The same execution and work bound recover all instances with a stronger stability promise. -/
lemma recoversWithin_mono {P : MinSumFPT.Program} {n k budget : ℕ}
    {d : Point n → Point n → ℝ} (hd : IsMetricArray d)
    {α β : ℝ} (hαβ : α ≤ β)
    (hrec : RecoversWithin P n k d α budget) :
    RecoversWithin P n k d β budget := by
  rcases hrec with ⟨t, ht, hh, hw, hl, hf, ho⟩
  exact ⟨t, ht, hh, hw, hl, hf, fun O hO => ho O (stable_mono hd hαβ hO)⟩

/-- In particular, the factor 3/2 algorithm suffices whenever γ is at least 2. -/
lemma recoversWithin_of_two_le {P : MinSumFPT.Program} {n k budget : ℕ}
    {d : Point n → Point n → ℝ} (hd : IsMetricArray d)
    {γ : ℝ} (hγ : 2 ≤ γ)
    (hrec : RecoversWithin P n k d (3 / 2) budget) :
    RecoversWithin P n k d γ budget := by
  exact recoversWithin_mono hd (by linarith) hrec

end CalibrationAux
end StableMSR.Recovery

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery

/-- Range checking and surjectivity of the output labels supply the feasibility
obligation in the public recovery specification. -/
lemma recoversWithin_of_labels
    (hdecode : ∀ {n k : ℕ} (s : MinSumFPT.State),
      ValidLabels n k s → Feasible Finset.univ k (outputPartition n k s))
    {P : MinSumFPT.Program} {n k budget : ℕ} {d : Point n → Point n → ℝ}
    {γ : ℝ}
    (hexec : ∃ t ≤ budget,
      let s := execute P n k d t
      s.halted = true ∧ s.work ≤ budget ∧ ValidLabels n k s ∧
        ∀ O, Stable d k γ O → outputPartition n k s = O) :
    RecoversWithin P n k d γ budget := by
  obtain ⟨t, ht, hh, hw, hl, ho⟩ := hexec
  exact ⟨t, ht, hh, hw, hl, hdecode _ hl, ho⟩

/-- The real stability theorem reduces to a uniform rational-parameter program,
the numerical parameter envelope, and the exact output-label decoding theorem.
All program, input, execution, and budget quantifiers remain in their original order. -/
theorem deterministic_exact_recovery_of_rational_program
    (henvelope : ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (parameterEnvelope ε : ℝ) ≤ K / ε ^ 5)
    (hdecode : ∀ {n k : ℕ} (s : MinSumFPT.State),
      ValidLabels n k s → Feasible Finset.univ k (outputPartition n k s))
    (hprogram :
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
        ∀ ε₀ : ℚ, 0 < ε₀ → ε₀ < 1 →
          ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
            ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
              1 ≤ k → k ≤ n → IsMetricArray d →
              ∃ t ≤ a * n ^ (b * parameterEnvelope (ε₀ : ℝ)),
                let s := execute P n k d t
                s.halted = true ∧
                  s.work ≤ a * n ^ (b * parameterEnvelope (ε₀ : ℝ)) ∧
                  ValidLabels n k s ∧
                  ∀ O, Stable d k (1 + (ε₀ : ℝ)) O → outputPartition n k s = O) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        ((γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5)) ∧
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            RecoversWithin P n k d γ (a * n ^ (b * parameterEnvelope (ε₀ : ℝ))) := by
  obtain ⟨a, b, ha, hb, hprogram⟩ := hprogram
  obtain ⟨K, hK, hE⟩ := henvelope
  obtain ⟨C, hC, hcal⟩ := CalibrationAux.exists_calibration_with_envelope K hK hE
  refine ⟨a, b, ha, hb, C, hC, ?_⟩
  intro γ hγ
  obtain ⟨ε₀, hεpos, hεone, hrange, hbound, hmargin⟩ := hcal γ hγ
  obtain ⟨P, hP, hrun⟩ := hprogram ε₀ hεpos hεone
  refine ⟨ε₀, hεpos, hεone, hrange, hbound, P, hP, ?_⟩
  intro n k d hk hkn hd
  exact CalibrationAux.recoversWithin_mono hd hmargin.le
    (recoversWithin_of_labels hdecode (hrun n k d hk hkn hd))

end StableMSR.Recovery
open StableMSR.Recovery

theorem StableMSR.Recovery.MissionReduction.fromDense (dense : ∃c D b:ℕ,0<c ∧ 0<b ∧ ∀e:ℚ,0<e → e<1 → ∃cmd:StableMSR.Recovery.Compiler.Cmd,StableMSR.Recovery.SingleRAM.denseSpec e c D b cmd) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        ((γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5)) ∧
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            RecoversWithin P n k d γ (a * n ^ (b * parameterEnvelope (ε₀ : ℝ))) := by
  exact deterministic_exact_recovery_of_rational_program
    parameterEnvelope_bound validLabels_feasible (StableMSRCompiledRecoveryStage11.fromDense dense)
end FinalCalibration

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
theorem solution (evaluated :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1≤x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∃F t,F≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    CandidateRAM.run F [CandidateRAM.code (budget (e:ℝ)) (widthBound (e:ℝ))] (CandidateRAM.banks s)=some t ∧
    (∀q:ℤ,(∀i:ℕ,q≠cell 5 i ∧ q≠cell 7 i) → t.mem q=s.imem q) ∧
    Candidates.Input x.n t.mem (tape CandidateRAM.Naming.name (Canonical.integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ)))) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ C : ℝ, 0 < C ∧
      ∀ γ : ℝ, 1 < γ → ∃ ε₀ : ℚ, 0 < ε₀ ∧ ε₀ < 1 ∧
        (if γ < 2 then (γ - 1) / 2 ≤ (ε₀ : ℝ) ∧ (ε₀ : ℝ) < γ - 1
         else ε₀ = 1 / 2) ∧
        ((γ < 2 → (parameterEnvelope (ε₀ : ℝ) : ℝ) ≤ C / (γ - 1) ^ 5)) ∧
        ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
          ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
            1 ≤ k → k ≤ n → IsMetricArray d →
            RecoversWithin P n k d γ (a * n ^ (b * parameterEnvelope (ε₀ : ℝ))) := by
  apply StableMSR.Recovery.MissionReduction.fromDense
  apply Canonical.dense_of_native_source
  exact CandidateRAM.native_source_of_evaluation evaluated
