-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.bounded_run_is_native
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:24:45.693044+00:00
-- url     : https://prove2.me/submissions/6feb8520-c941-4a2c-a8b4-95e1138192ee

import Definitions.Def_StableMSR_CandidateInterpreter
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open Compiler
set_option autoImplicit false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

theorem op_agrees {n:ℕ} (d:Fin n→Fin n→ℝ) (o:IOp) (s:Store) (b:Banks) :
    o.lower.eval d (restore s b)=restore s (o.act b):=by cases o <;> rfl

inductive Chain {n:ℕ} (d:Fin n→Fin n→ℝ) : List Code→Store→Store→ℕ→Prop where
  | nil (s:Store) : Chain d [] s s 0
  | cons {p:Code} {ps:List Code} {s t u:Store} {z y:ℕ} :
      Executes d p.lower s t z → Chain d ps t u y → Chain d (p::ps) s u (z+y)
theorem uncons {n:ℕ} {d:Fin n→Fin n→ℝ} {p:Code} {ps:List Code} {s t:Store} {z:ℕ}
    (ex:Chain d (p::ps) s t z) :
    ∃u i j,Executes d p.lower s u i ∧ Chain d ps u t j ∧ z=i+j:=by
  cases ex with | cons a b=>exact ⟨_,_,_,a,b,rfl⟩

theorem run_chain {n:ℕ} (d:Fin n→Fin n→ℝ) (base:Store) (fuel:ℕ) (ps:List Code) (s t:Banks)
    (ok:run fuel ps s=some t) : ∃z,Chain d ps (restore base s) (restore base t) z ∧ z≤2*fuel:=by
  induction fuel generalizing ps s with
  | zero=>cases ps with
    | nil=>simp [run] at ok;subst t;exact ⟨_,.nil _,by omega⟩
    | cons p ps=>simp [run] at ok
  | succ f ih=>
    cases ps with
    | nil=>simp [run] at ok;subst t;exact ⟨_,.nil _,by omega⟩
    | cons p ps=>
      cases p with
      | skip=>obtain ⟨z,tail,tm⟩:=ih ps s ok;exact ⟨_,.cons (.skip _) tail,by omega⟩
      | atom o=>
        obtain ⟨z,tail,tm⟩:=ih ps (o.act s) ok
        have step:Executes d (Code.atom o).lower (restore base s) (restore base (o.act s)) 1:=by
          rw [←op_agrees d o base s];exact .atom _ _
        exact ⟨_,.cons step tail,by omega⟩
      | seq p q=>
        obtain ⟨z,chain,tm⟩:=ih (p::q::ps) s ok
        obtain ⟨u,i,y,first,more,eq⟩:=uncons chain
        obtain ⟨v,j,k,second,last,eq'⟩:=uncons more
        exact ⟨_,.cons (.seq first second) last,by omega⟩
      | cond a b p q=>
        by_cases flag:s.reg a ≤ s.reg b
        · obtain ⟨z,chain,tm⟩:=ih (p::ps) s (by simpa only [run,if_pos flag] using ok)
          obtain ⟨u,i,j,first,tail,eq⟩:=uncons chain
          exact ⟨_,.cons (.ite_true flag first) tail,by omega⟩
        · obtain ⟨z,chain,tm⟩:=ih (q::ps) s (by simpa only [run,if_neg flag] using ok)
          obtain ⟨u,i,j,first,tail,eq⟩:=uncons chain
          exact ⟨_,.cons (.ite_false flag first) tail,by omega⟩
      | loop a b p=>
        by_cases flag:s.reg a ≤ s.reg b
        · obtain ⟨z,chain,tm⟩:=ih (p::.loop a b p::ps) s (by simpa only [run,if_pos flag] using ok)
          obtain ⟨u,i,y,first,more,eq⟩:=uncons chain
          obtain ⟨v,j,k,again,tail,eq'⟩:=uncons more
          exact ⟨_,.cons (.while_true flag first again) tail,by omega⟩
        · obtain ⟨z,tail,tm⟩:=ih ps s (by simpa only [run,if_neg flag] using ok)
          exact ⟨_,.cons (.while_false flag) tail,by omega⟩

theorem singleton {n:ℕ} (d:Fin n→Fin n→ℝ) (cmd:Code) (s:Store) (fuel:ℕ) (t:Banks)
    (ok:run fuel [cmd] (banks s)=some t) :
    ∃z,Executes d cmd.lower s (restore s t) z ∧ z≤2*fuel:=by
  obtain ⟨total,chain,bound⟩:=run_chain d s fuel _ _ _ ok
  obtain ⟨v,z,j,ex,tail,eq⟩:=uncons chain
  cases tail
  exact ⟨z,ex,by omega⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open Compiler
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 4200000
theorem act_low (o:IOp) (s:Banks) (yes:o.low=true) (j:ℕ) (hj:j<6) : (o.act s).reg j=s.reg j:=by
  cases o <;> simp_all [IOp.act,IOp.low,Banks.put,Banks.write,Function.update_apply] <;> intro eq <;> omega
theorem run_low (fuel:ℕ) (ps:List Code) (s t:Banks) (h:run fuel ps s=some t) (good:∀p∈ps,p.low=true)
    (j:ℕ) (hj:j<6) : t.reg j=s.reg j:=by
  induction fuel generalizing ps s with
  | zero=>cases ps <;> simp [run] at h;rw [h]
  | succ f ih=>
    cases ps with
    | nil=>simp [run] at h;rw [h]
    | cons p ps=>
      have hp:=good p List.mem_cons_self
      have tail:∀v∈ps, v.low=true:=fun v hv=>good _ (List.mem_cons_of_mem _ hv)
      cases p with
      | skip=>exact ih _ _ h tail
      | atom o=>exact (ih _ _ h tail).trans (act_low o s hp j hj)
      | seq p q=>
        have both:=Bool.and_eq_true_iff.mp hp
        apply ih _ _ h
        simp only [List.mem_cons];rintro v (rfl|rfl|p) <;> first | exact both.1 | exact both.2 | exact tail _ p
      | cond a b p q=>
        have both:=Bool.and_eq_true_iff.mp hp
        by_cases bound:s.reg a ≤ s.reg b
        · apply ih (p::ps) s (by simpa only [run,if_pos bound] using h);simp only [List.mem_cons];rintro v (rfl|hv) <;> first | exact both.1 | exact tail _ hv
        · apply ih (q::ps) s (by simpa only [run,if_neg bound] using h);simp only [List.mem_cons];rintro v (rfl|hv) <;> first | exact both.2 | exact tail _ hv
      | loop a b p=>
        by_cases bound:s.reg a ≤ s.reg b
        · apply ih (p::.loop a b p::ps) s (by simpa only [run,if_pos bound] using h)
          simp only [List.mem_cons];rintro v (rfl|rfl|hv) <;> first | exact hp | exact tail _ hv
        · exact ih ps s (by simpa only [run,if_neg bound] using h) tail

/-- None of the emitted commands assigns an input or incoming region register. -/
theorem program_low (h w:ℕ) : (code h w).low=true:=by
  have body:proc_generate.low=true:=by decide
  simpa only [code,seqs,List.foldr,Code.low,IOp.low,setc,cp,body]
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM


open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution {n:ℕ} (d:Fin n→Fin n→ℝ) (s:Store) (h w fuel:ℕ) (t:CandidateRAM.Banks)
  (done:CandidateRAM.run fuel [CandidateRAM.code h w] (CandidateRAM.banks s)=some t) :
  ∃z,Executes d (CandidateRAM.program h w) s (CandidateRAM.restore s t) z ∧ z≤2*fuel ∧
  (∀j<6,t.reg j=s.ptrs j) := by
  obtain ⟨z,ex,tm⟩:=CandidateRAM.singleton d _ s fuel t done
  refine ⟨z,ex,tm,?_⟩
  intro j hj
  exact CandidateRAM.run_low fuel _ _ t done (by simp [CandidateRAM.program_low]) j hj
