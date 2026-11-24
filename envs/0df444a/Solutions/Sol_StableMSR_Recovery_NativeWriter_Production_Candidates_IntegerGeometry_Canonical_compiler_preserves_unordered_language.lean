-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.compiler_preserves_unordered_language
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:01:27.61055+00:00
-- url     : https://prove2.me/submissions/872499f7-2c80-4c49-8275-00ce50e19641

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
import Theorems.Thm_StableMSR_Recovery_SingleCircuit_regional_compiler_trace_language
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

noncomputable def emit (n:ℕ) (m:List ℕ) := WindowMasks.emit (Finset.univ.filter (fun i:Fin n=>m.contains i.val))
noncomputable def out (d:Instance) (n:ℕ) (t:Letter) := (d.owned t.1 t.2).flatMap (emit n)
def TraceLaw := ∀(n:ℕ) (d:Instance) (w:ℕ),let g:=compileRegion d w
  g.2<g.1.size ∧ ∀s,Language n g.1 g.2 s ↔ ∃t,traces d w t ∧ s=t.flatMap (out d n)

theorem emit_points (n:ℕ) (ls:List ℕ) : emit n (pointList ls)=emit n ls:=by
  unfold emit;congr 1;ext i;simp [pointList]
theorem output_perm (d:Instance) (n:ℕ) (t:Letter) : (out (arrange d) n t).Perm (out d n t):=by
  let ms:=d.owned t.1 t.2
  have p:=List.Perm.flatMap_right (emit n) (List.mergeSort_perm (ms.map pointList) (fun a b=>decide (a≤b)))
  simpa only [out,arrange,blockList,List.flatMap_map,Function.comp_def,emit_points,ms] using p

theorem word_perm (d:Instance) (n:ℕ) (w:List Letter) :
    (w.flatMap (out (arrange d) n)).Perm (w.flatMap (out d n)):=by
  induction w with
  | nil=>rfl
  | cons l ls ih=>exact (output_perm d n l).append ih

theorem assignments_arrange (d:Instance) (s:List ℕ) : assignments (arrange d) s=assignments d s:=by
  induction s with | nil=>rfl | cons v s ih=>simp only [assignments,ih];rfl
theorem visits_arrange (d:Instance) (k:ℕ) (s c:List ℕ) (z:Unit×Table (Lang Letter)) :
    visit wordAlgebra (arrange d) k s c z=visit wordAlgebra d k s c z:=by
  unfold visit;rw [assignments_arrange];rfl
theorem traces_arrange (d:Instance) (w:ℕ) : traces (arrange d) w=traces d w:=by
  unfold traces scan build;simp only [visits_arrange];rfl

theorem compiled_equiv (law:TraceLaw) (n:ℕ) (d:Instance) (w:ℕ) :
    let g:=compileRegion (arrange d) w
    let t:=compileRegion d w
    g.2<g.1.size ∧ Equivalent n g.1 g.2 t.1 t.2:=by
  have sorted:=law n (arrange d) w
  have orig:=law n d w
  refine ⟨sorted.1,?_,?_⟩
  · intro L h;obtain ⟨v,hv,rfl⟩:=(sorted.2 L).mp h
    exact ⟨_,(orig.2 _).mpr ⟨v,traces_arrange d w ▸ hv,rfl⟩,word_perm d n v⟩
  · intro K h;obtain ⟨v,hv,rfl⟩:=(orig.2 K).mp h
    exact ⟨_,(sorted.2 _).mpr ⟨v,(traces_arrange d w).symm ▸ hv,rfl⟩,word_perm d n v⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution (n:ℕ) (d:Instance) (w:ℕ) :
  let g:=compileRegion (Canonical.arrange d) w
  let t:=compileRegion d w
  g.2<g.1.size ∧ Canonical.Equivalent n g.1 g.2 t.1 t.2 := Canonical.compiled_equiv SingleCircuit.regional_compiler_trace_language n d w
