-- Prove2me | solution 1 for StableMSR.Recovery.SingleSearch.singleton_labelled_component_language
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:13:20.159655+00:00
-- url     : https://prove2.me/submissions/b14e8cd6-64fd-4ff7-8b81-87bb1c863e94

import Definitions.Def_StableMSR_SingleVertexSearch
import Theorems.Thm_StableMSR_Recovery_SingleSearch_deletion_piece_geometry
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
    (G : SimpleGraph V) (D : V→Finset X) (test : V→V→X→X→Prop) (w m : ℕ) (S C : Finset V)
    (hc : IsFlap G S C) (a : V→X) (O : Finset (V×X)) :
    run G D test w m S C a O ↔ one G w m S C ∧ ∃f : V→X,
      okay G D test (S∪C) f ∧ (∀v∈S,f v=a v) ∧ O=labels C f := by
  classical
  induction m generalizing S C a O with
  | zero=>simp [run,one]
  | succ m ih=>
    have data (v : V) (hv : v∈C) := deletion_piece_geometry G S C (insert v S) hc (Finset.subset_insert ..)
      (Finset.insert_subset (Finset.mem_union_right _ hv) Finset.subset_union_left)
    have assembly (v : V) (hv : v∈C) (f : V→X) (L : Finset V→Finset (V×X))
        (h : ∀E∈children G (insert v S) C,L E=labels E f) :
        insert (v,f v) ((children G (insert v S) C).biUnion L)=labels C f:=by
      have reconstruct : insert v ((children G (insert v S) C).biUnion id)=C:=by
        rw [(data v hv).1];ext z;by_cases eq : z=v
        · subst z;simp [hv]
        · by_cases cz : z∈C
          · have ns : z∉S:=fun h=>Finset.disjoint_left.mp hc.avoids h cz
            simp [cz,ns,eq]
          · simp [cz,eq]
      calc
        _ = insert (v,f v) (labels ((children G (insert v S) C).biUnion id) f):=congrArg (insert (v,f v)) (unionLabels _ f L h)
        _ = labels (insert v ((children G (insert v S) C).biUnion id)) f:=by simp [labels,Finset.image_insert]
        _ = labels C f:=congrArg (fun U=>labels U f) reconstruct
    constructor
    · rintro ⟨sw,v,hv,x,bet,outs,child,eqO⟩
      let B:=insert v S;let b:=Function.update a v x;let K:=children G B C
      have dat:=data v hv
      have each (E : Finset V) (he : E∈K) := (ih (boundary G E) E (dat.2.2.1 E he).1 b (outs E)).mp (child E he).2
      have can : one G w (m+1) S C:=⟨sw,v,hv,fun E he=>⟨(child E he).1,(each E he).1⟩⟩
      choose ff ffprop using fun E : ↥K=>(each E.val E.property).2
      let f (E : Finset V) : V→X:=if he : E∈K then ff ⟨E,he⟩ else a
      have specs (E : Finset V) (he : E∈K) : okay G D test (boundary G E∪E) (f E) ∧
          (∀z∈boundary G E,f E z=b z) ∧ outs E=labels E (f E):=by simpa only [f,dif_pos he] using ffprop ⟨E,he⟩
      have locally (E : Finset V) (he : E∈K) : okay G D test (E∪rim G (total B K) E) (patch E b (f E)):=by
        rw [dat.2.1,(dat.2.2.1 E he).2.2.2,Finset.union_comm]
        apply okOn (specs E he).1 (Finset.Subset.refl _)
        intro z hz;by_cases yes : z∈E
        · simp [patch,yes]
        · have bd:= (Finset.mem_union.mp hz).resolve_right yes
          simpa [patch,yes] using (specs E he).2.1 z bd
      obtain ⟨g,allOK,onB,onE⟩:=(separator_assignment_factorization G D test B K (fun E he=>(dat.2.2.1 E he).2.1) dat.2.2.2 b f).mpr ⟨bet,locally⟩
      have gv : g v=x:=by simpa [b] using onB v (Finset.mem_insert_self ..)
      refine ⟨can,g,dat.2.1 ▸ allOK,?_,?_⟩
      · intro z hz;have ne : z≠v:=fun e=>Finset.disjoint_left.mp hc.avoids (e ▸ hz) hv
        simpa [b,Function.update_of_ne ne] using onB z (Finset.mem_insert_of_mem hz)
      · rw [eqO,←gv];apply assembly v hv g outs;intro E he
        exact (specs E he).2.2.trans (sameLabels E (fun z hz=>(onE E he z hz).symm))
    · rintro ⟨⟨sw,v,hv,sub⟩,f,ok,bd,rfl⟩
      let B:=insert v S;let b:=Function.update a v (f v);let K:=children G B C
      have dat:=data v hv
      have inB : B⊆S∪C:=Finset.insert_subset (Finset.mem_union_right _ hv) Finset.subset_union_left
      have matchB (z : V) (hz : z∈B) : f z=b z:=by
        rcases Finset.mem_insert.mp hz with rfl|h
        · simp [b]
        · have ne : z≠v:=fun e=>Finset.disjoint_left.mp hc.avoids (e ▸ h) hv
          simpa [b,Function.update_of_ne ne] using bd z h
      refine ⟨sw,v,hv,f v,okOn ok inB matchB,(fun E=>labels E f),?_,(assembly v hv f _ (fun _ _=>rfl)).symm⟩
      intro E he;have z:=dat.2.2.1 E he
      refine ⟨(sub E he).1,(ih _ _ z.1 b _).mpr ⟨(sub E he).2,f,?_,fun v hv=>matchB v (z.2.2.1 hv),rfl⟩⟩
      apply okOn ok _ (fun _ _=>rfl)
      exact Finset.union_subset (fun _ h=>inB (z.2.2.1 h)) (fun _ h=>Finset.mem_union_right _ ((mem_children.mp he).2 h))
