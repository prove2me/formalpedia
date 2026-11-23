-- Prove2me | solution 1 for StableMSR.Recovery.SingleWindows.singleton_grammar_exact_window_partitions
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:12:22.275806+00:00
-- url     : https://prove2.me/submissions/fd23e22f-7a53-43e7-8a9e-c7172b73b0d5

import Definitions.Def_StableMSR_SingleWindowGrammar
import Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_full_assignment_language
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
private lemma projLabels (x : World) (W : Cluster x.n) (R : ℝ) (P : Pick x.n) :
    project x W R (labels Finset.univ (fun v : SingleWindows.Vertex x W R=>P v))=WindowCSP.output x W R P:=by
  classical
  ext C;constructor
  · intro h;obtain ⟨z,hz,mem⟩:=Finset.mem_biUnion.mp h
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hz
    exact Finset.mem_biUnion.mpr ⟨v.val,v.property,mem⟩
  · intro h;obtain ⟨v,hv,mem⟩:=Finset.mem_biUnion.mp h
    let a : SingleWindows.Vertex x W R:=⟨v,hv⟩
    exact Finset.mem_biUnion.mpr ⟨(a,P v),Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,mem⟩
theorem solution (x : World) (W : Cluster x.n) (R : ℝ) (h w : ℕ) (Q : Partition x.n) :
    generates x W R h w Q ↔ TreewidthLE (interactionGraph x.dist R W) w ∧
      ∃P : Pick x.n,valid x W R h P ∧ WindowCSP.output x W R P=Q := by
  classical
  let N:=greedyNet x.dist R W;let G:=interactionGraph x.dist R W
  let A:=domains x W R h;let test:=constraint x W R
  let emptyLabel : SingleWindows.Vertex x W R→Partition x.n:=fun _=>∅
  constructor
  · rintro ⟨O,found,eq⟩
    obtain ⟨tw,f,ok,rfl⟩:=(singleton_full_assignment_language G A test w emptyLabel O).mp found
    let P : Pick x.n:=fun a=>if ha:a∈N then f ⟨a,ha⟩ else ∅
    have on (a : SingleWindows.Vertex x W R) : P a=f a:=by simp [P,N,a.property]
    have labelEq : (fun a : SingleWindows.Vertex x W R=>P a)=f:=funext on
    refine ⟨tw,P,⟨?_,?_⟩,?_⟩
    · intro a ha;let v : SingleWindows.Vertex x W R:=⟨a,ha⟩
      exact (on v).symm ▸ ok.1 v (Finset.mem_univ _)
    · intro a b ed;rw [on a,on b];exact ok.2 a (Finset.mem_univ _) b (Finset.mem_univ _) ed
    · rw [←eq,←labelEq,projLabels]
  · rintro ⟨tw,P,ok,rfl⟩
    let f : SingleWindows.Vertex x W R→Partition x.n:=fun a=>P a
    refine ⟨labels Finset.univ f,(singleton_full_assignment_language G A test w emptyLabel _).mpr ⟨tw,f,?_,rfl⟩,projLabels x W R P⟩
    exact ⟨fun a _=>ok.1 a a.property,fun a _ b _ ed=>ok.2 a b ed⟩
