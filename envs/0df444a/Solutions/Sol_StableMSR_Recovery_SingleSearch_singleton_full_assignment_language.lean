-- Prove2me | solution 1 for StableMSR.Recovery.SingleSearch.singleton_full_assignment_language
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:13:20.111167+00:00
-- url     : https://prove2.me/submissions/a44261ff-7893-4c61-b65e-68f2d3a4454d

import Definitions.Def_StableMSR_SingleVertexSearch
import Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_labelled_component_language
import Theorems.Thm_StableMSR_Recovery_SingleSearch_root_component_geometry
import Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_search_recognizes_treewidth
import Theorems.Thm_StableMSR_Recovery_WindowCuts_separator_assignment_factorization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
private lemma okOn {V X : Type} [DecidableEq V] {G : SimpleGraph V} {D : V→Finset X} {test : V→V→X→X→Prop}
    {A B : Finset V} {f g : V→X} (h : okay G D test A f) (sub : B⊆A) (same : ∀v∈B,f v=g v) : okay G D test B g:=by
  refine ⟨?_,?_⟩
  · intro v hv;rw [←same v hv];exact h.1 v (sub hv)
  · intro v hv u hu he;rw [←same v hv,←same u hu];exact h.2 v (sub hv) u (sub hu) he
private lemma sameLabels {V X : Type} [DecidableEq V] [DecidableEq X] (U : Finset V) {f g : V→X}
    (h : ∀v∈U,f v=g v) : labels U f=labels U g:=by
  apply Finset.image_congr;intro v hv;exact congrArg (Prod.mk v) (h v hv)
private lemma unionLabels {V X : Type} [DecidableEq V] [DecidableEq X] (K : Finset (Finset V)) (f : V→X)
    (L : Finset V→Finset (V×X)) (h : ∀E∈K,L E=labels E f) : K.biUnion L=labels (K.biUnion id) f:=by
  classical
  ext z;constructor
  · intro hz;obtain ⟨E,he,hz⟩:=Finset.mem_biUnion.mp hz
    rw [h E he] at hz;obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨u,Finset.mem_biUnion.mpr ⟨E,he,hu⟩,rfl⟩
  · intro hz;obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
    obtain ⟨E,he,hu⟩:=Finset.mem_biUnion.mp hu
    exact Finset.mem_biUnion.mpr ⟨E,he,h E he ▸ Finset.mem_image.mpr ⟨u,hu,rfl⟩⟩
theorem solution {V X : Type} [Fintype V] [DecidableEq V] [DecidableEq X]
    (G : SimpleGraph V) (D : V→Finset X) (test : V→V→X→X→Prop) (w : ℕ) (a : V→X) (O : Finset (V×X)) :
    root G D test w a O ↔ TreewidthLE G w ∧ ∃f : V→X,okay G D test Finset.univ f ∧ O=labels Finset.univ f := by
  classical
  let K:=PartialDecompositions.components G ∅
  have dat:=root_component_geometry G
  have univEq : total (∅ : Finset V) K=Finset.univ:=by rw [total,Finset.empty_union];exact dat.1
  have rimEq (C : Finset V) (hc : C∈K) : rim G (total (∅ : Finset V) K) C=∅:=by
    rw [univEq];have eq : rim G Finset.univ C=boundary G C:=by ext z;simp [rim,boundary]
    exact eq.trans (dat.2.1 C hc)
  constructor
  · rintro ⟨out,hout,rfl⟩
    have child (C : Finset V) (hc : C∈K) := (singleton_labelled_component_language G D test w _ ∅ C (mem_components.mp hc) a (out C)).mp (hout C hc)
    have wG : TreewidthLE G w:=(singleton_search_recognizes_treewidth G w).mp (fun C hc=>(child C hc).1)
    choose ff props using fun C : ↥K=>(child C.val C.property).2
    let f (C : Finset V) : V→X:=if hc:C∈K then ff ⟨C,hc⟩ else a
    have localF (C : Finset V) (hc : C∈K) : okay G D test C (f C) ∧ out C=labels C (f C):=by
      have h:=props ⟨C,hc⟩;simpa only [f,dif_pos hc,Finset.empty_union] using And.intro h.1 h.2.2
    have empty : okay G D test ∅ a:=⟨fun _ h=>False.elim (Finset.notMem_empty _ h),fun _ h=>False.elim (Finset.notMem_empty _ h)⟩
    have loc (C : Finset V) (hc : C∈K) : okay G D test (C∪rim G (total (∅ : Finset V) K) C) (patch C a (f C)):=by
      rw [rimEq C hc,Finset.union_empty]
      exact okOn (localF C hc).1 (Finset.Subset.refl C) (fun z hz=>by simp [patch,hz])
    obtain ⟨g,og,_,ong⟩:=(separator_assignment_factorization G D test ∅ K (fun _ _=>Finset.disjoint_empty_right _) dat.2.2 a f).mpr ⟨empty,loc⟩
    refine ⟨wG,g,univEq ▸ og,?_⟩
    calc
      K.biUnion out=labels (K.biUnion id) g:=unionLabels K g out (fun C hc=>(localF C hc).2.trans (sameLabels C (fun v hv=>(ong C hc v hv).symm)))
      _ = labels Finset.univ g:=congrArg (fun U=>labels U g) dat.1
  · rintro ⟨tw,f,hf,rfl⟩
    have ok:= (singleton_search_recognizes_treewidth G w).mpr tw
    refine ⟨(fun C=>labels C f),?_,?_⟩
    · intro C hc;apply (singleton_labelled_component_language G D test w _ ∅ C (mem_components.mp hc) a _).mpr
      exact ⟨ok C hc,f,okOn hf (Finset.subset_univ _) (fun _ _=>rfl),fun _ h=>False.elim (Finset.notMem_empty _ h),rfl⟩
    · rw [unionLabels K f _ (fun _ _=>rfl),dat.1]
