-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.computed_integer_instance
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T00:57:42.886997+00:00
-- url     : https://prove2.me/submissions/7c5640e8-bc38-420b-bdf4-cd68eaed56b4

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Bits_executable_window_fields
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_integer_instance_exact
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP SingleWindows TightLanguage
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem sorted_eq {xs ys:List (List ℕ)} (h:Bits.MasksAgree xs ys) : blockList xs=blockList ys:=by
  let le:=fun a b:List ℕ=>decide (a≤b)
  have fm (ls:List (List ℕ)) : (ls.map List.toFinset).map (fun a:Finset ℕ=>a.sort (·≤·))=ls.map pointList:=by
    induction ls with | nil=>rfl | cons x xs ih=>simp only [List.map_cons,ih];rfl
  have p:(xs.map pointList).Perm (ys.map pointList):=by
    simpa only [←fm] using (h.map (fun a:Finset ℕ=>a.sort (·≤·)))
  apply ((List.mergeSort_perm _ le).trans (p.trans (List.mergeSort_perm _ le).symm)).eq_of_pairwise' (r:=(·≤·))
  · exact List.pairwise_mergeSort' _ _
  · exact List.pairwise_mergeSort' _ _

theorem arrange_eq {d t:Instance} (sz:d.n=t.n) (ac:d.active=t.active) (ed:d.edge=t.edge) (mn:d.menu=t.menu) (te:d.test=t.test)
    (masks:∀a c,Bits.MasksAgree (d.owned a c) (t.owned a c)) : arrange d=arrange t:=by
  have owned:(fun a c=>blockList (d.owned a c))=(fun a c=>blockList (t.owned a c)):=by funext a c;exact sorted_eq (masks a c)
  cases d;cases t;simp only [arrange] at *;congr 1 <;> assumption
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution (x:World) (r h:ℕ) (m:ℤ→ℤ)
  (hn:0<x.n) (pos:0<scale x (r/x.n)) (metric:IsMetricArray x.dist) (prep:Prepared x (scale x (r/x.n)) m) :
  Canonical.integerData x.n x.mem m r h = Canonical.arrange (SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) h) := by
  obtain ⟨hn',ac,ed,mn,te,ms⟩:=Bits.executable_window_fields x m r h
  have a:=Canonical.arrange_eq hn' ac ed mn te ms
  change Canonical.integerData x.n x.mem m r h=Canonical.arrange (data x m r h) at a
  rw [a]
  exact congrArg Canonical.arrange (integer_instance_exact x _ _ h m hn pos metric prep).1
