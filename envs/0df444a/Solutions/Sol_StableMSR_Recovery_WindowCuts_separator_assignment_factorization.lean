-- Prove2me | solution 1 for StableMSR.Recovery.WindowCuts.separator_assignment_factorization
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:41:02.142176+00:00
-- url     : https://prove2.me/submissions/65638eeb-4f91-44ae-91a0-0d296d2571bf

import Definitions.Def_StableMSR_WindowSeparatorCuts
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowCuts
theorem solution {V X : Type} [DecidableEq V] (G : SimpleGraph V) (D : V→Finset X) (test : V→V→X→X→Prop)
    (T : Finset V) (K : Finset (Finset V))
    (away : ∀C∈K,Disjoint C T)
    (split : ∀C∈K,∀E∈K,C≠E → Disjoint C E ∧ ∀v∈C,∀w∈E,¬G.Adj v w)
    (a : V→X) (f : Finset V→V→X) :
    (∃g : V→X,okay G D test (total T K) g ∧ (∀v∈T,g v=a v) ∧ ∀C∈K,∀v∈C,g v=f C v) ↔
      okay G D test T a ∧ ∀C∈K,okay G D test (C∪rim G (total T K) C) (patch C a (f C)) := by
  classical
  let U:=total T K
  have into (C : Finset V) (h : C∈K) {v : V} (hv : v∈C) : v∈U:=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C,h,hv⟩)
  have bagIn {v : V} (hv : v∈T) : v∈U:=Finset.mem_union_left _ hv
  have rimIn (C : Finset V) (hc : C∈K) {v : V} (hv : v∈rim G U C) : v∈T:=by
    obtain ⟨vu,vc,w,wc,edge⟩:=Finset.mem_filter.mp hv
    rcases Finset.mem_union.mp vu with yes|inside
    · exact yes
    · obtain ⟨E,he,ve⟩:=Finset.mem_biUnion.mp inside
      have diff : C≠E:=fun eq=>vc (eq.symm ▸ ve)
      exact ((split C hc E he diff).2 w wc v ve edge).elim
  have regionIn (C : Finset V) (hc : C∈K) {v : V} (hv : v∈C∪rim G U C) : v∈U:=by
    rcases Finset.mem_union.mp hv with h|h
    · exact into C hc h
    · exact (Finset.mem_filter.mp h).1
  have localEq {g : V→X} (ba : ∀v∈T,g v=a v) (ins : ∀C∈K,∀v∈C,g v=f C v) (C : Finset V) (hc : C∈K)
      {v : V} (hv : v∈C∪rim G U C) : g v=patch C a (f C) v:=by
    by_cases h : v∈C
    · simpa [patch,h] using ins C hc v h
    · have mem : v∈rim G U C:=(Finset.mem_union.mp hv).resolve_left h
      simpa [patch,h] using ba v (rimIn C hc mem)
  have restrict {S T' : Finset V} {f g : V→X} (inc : S⊆T') (eq : ∀v∈S,f v=g v)
      (ok : okay G D test T' f) : okay G D test S g:=by
    refine ⟨?_,?_⟩
    · intro v hv;rw [←eq v hv];exact ok.1 v (inc hv)
    · intro v hv w hw edge;rw [←eq v hv,←eq w hw];exact ok.2 v (inc hv) w (inc hw) edge
  constructor
  · rintro ⟨g,ok,ba,ins⟩
    exact ⟨restrict (fun _ h=>bagIn h) ba ok,fun C hc=>restrict (fun _ h=>regionIn C hc h) (fun _ h=>localEq ba ins C hc h) ok⟩
  · rintro ⟨root,localOK⟩
    let g (v : V):=if h : ∃C∈K,v∈C then f h.choose v else a v
    have ba (v : V) (hv : v∈T) : g v=a v:=by
      apply dif_neg; rintro ⟨C,hc,mem⟩;exact Finset.disjoint_left.mp (away C hc) mem hv
    have ins (C : Finset V) (hc : C∈K) (v : V) (hv : v∈C) : g v=f C v:=by
      have hit : ∃E∈K,v∈E:=⟨C,hc,hv⟩
      have idx : hit.choose=C:=by
        by_contra ne
        exact Finset.disjoint_left.mp (split _ hit.choose_spec.1 C hc ne).1 hit.choose_spec.2 hv
      unfold g;rw [dif_pos hit,idx]
    have localG (C : Finset V) (hc : C∈K) : okay G D test (C∪rim G U C) g:=
      restrict (Finset.Subset.refl _) (fun _ hv=>(localEq ba ins C hc hv).symm) (localOK C hc)
    have covers {C : Finset V} {v w : V} (h : v∈C) (wu : w∈U) (edge : G.Adj v w) : w∈C∪rim G U C:=by
      by_cases yes : w∈C
      · exact Finset.mem_union_left _ yes
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨wu,yes,v,h,edge⟩)
    refine ⟨g,⟨?_,?_⟩,ba,ins⟩
    · intro v hv;rcases Finset.mem_union.mp hv with h|h
      · rw [ba v h];exact root.1 v h
      · obtain ⟨C,hc,vc⟩:=Finset.mem_biUnion.mp h;exact (localG C hc).1 v (Finset.mem_union_left _ vc)
    · intro v hv w hw edge;rcases Finset.mem_union.mp hv with vb|child
      · rcases Finset.mem_union.mp hw with wb|wb
        · rw [ba v vb,ba w wb];exact root.2 v vb w wb edge
        · obtain ⟨C,hc,wc⟩:=Finset.mem_biUnion.mp wb
          exact (localG C hc).2 v (covers wc hv edge.symm) w (Finset.mem_union_left _ wc) edge
      · obtain ⟨C,hc,vc⟩:=Finset.mem_biUnion.mp child
        exact (localG C hc).2 v (Finset.mem_union_left _ vc) w (covers vc hw edge) edge
