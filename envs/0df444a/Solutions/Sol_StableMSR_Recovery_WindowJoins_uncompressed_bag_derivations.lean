-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.uncompressed_bag_derivations
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:48:54.101657+00:00
-- url     : https://prove2.me/submissions/1bfc3af0-2a04-4f6f-abc4-f2fc126f3b71

import Definitions.Def_StableMSR_WindowJoinTemplates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery.TreeDP StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds
private lemma cheaper {V X : Type} (k : ℕ) (A : Finset (Entry V X)) (a : V→X) (j : ℕ) (w : ℝ)
    (h : (a,(j,w))∈A) (hj : j≤ k) : ∃z≤ w,(a,(j,z))∈minimize (trim k A):=by
  classical
  let B:=trim k A;let S:=B.filter (fun u=>u.1=a ∧ u.2.1=j)
  have base : (a,(j,w))∈B:=Finset.mem_filter.mpr ⟨h,hj⟩
  have mem : (a,(j,w))∈S:=Finset.mem_filter.mpr ⟨base,rfl,rfl⟩
  obtain ⟨⟨b,i,t⟩,sel,least⟩:=Finset.exists_min_image S (fun u=>u.2.2) ⟨_,mem⟩
  obtain ⟨hb,eq,eq'⟩:=Finset.mem_filter.mp sel
  change b=a at eq;change i=j at eq';subst b;subst i
  refine ⟨t,least _ mem,Finset.mem_filter.mpr ⟨hb,?_⟩⟩
  intro c hc first cnt;exact least c (Finset.mem_filter.mpr ⟨hc,first,cnt⟩)
private lemma sound {V X : Type} [DecidableEq V] (cap : ℕ) (p : Plan V X) :
    ∀u∈TreeDP.solve cap p,Raw cap p u.1 u.2.1 u.2.2:=by
  induction p with
  | leaf d =>
    intro u hu;obtain ⟨trimmed,_⟩:=Finset.mem_filter.mp hu;obtain ⟨inA,lim⟩:=Finset.mem_filter.mp trimmed
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp inA;obtain ⟨dom,test⟩:=Finset.mem_filter.mp ha
    exact .leaf d a dom test lim
  | branch d L R il ir =>
    intro u hu;obtain ⟨trimmed,_⟩:=Finset.mem_filter.mp hu;obtain ⟨inA,lim⟩:=Finset.mem_filter.mp trimmed
    obtain ⟨⟨⟨a,b⟩,c⟩,pass,rfl⟩:=Finset.mem_image.mp inA
    obtain ⟨data,agreeL,agreeR⟩:=Finset.mem_filter.mp pass
    obtain ⟨dl,cr⟩:=Finset.mem_product.mp data;obtain ⟨ad,bl⟩:=Finset.mem_product.mp dl
    obtain ⟨dom,test⟩:=Finset.mem_filter.mp ad
    exact .join d a b.1 c.1 dom test agreeL agreeR (il b bl) (ir c cr) lim
theorem solution {V X : Type} [DecidableEq V] (cap : ℕ) (p : Plan V X) :
    (∀u∈TreeDP.solve cap p,Raw cap p u.1 u.2.1 u.2.2) ∧
    ∀a j w,Raw cap p a j w → ∃t≤ w,(a,(j,t))∈TreeDP.solve cap p := by
  classical
  refine ⟨sound cap p,?_⟩;intro a j w der
  induction der with
  | leaf d a dom test capOK =>
    apply cheaper cap (leafEntries d) _ _ _ _ capOK
    exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨dom,test⟩,rfl⟩
  | @join d L R a b c i j s t dom test al ar dl dr capOK il ir =>
    obtain ⟨u,us,um⟩:=il;obtain ⟨v,vt,vm⟩:=ir
    let A:=joinEntries d L.root.bag R.root.bag (TreeDP.solve cap L) (TreeDP.solve cap R)
    have member : (a,(d.count a+i+j,d.weight a+u+v))∈A:=by
      apply Finset.mem_image.mpr;refine ⟨((a,(b,(i,u))),(c,(j,v))),Finset.mem_filter.mpr ⟨?_,al,ar⟩,rfl⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨dom,test⟩,um⟩,vm⟩
    obtain ⟨z,zle,done⟩:=cheaper cap A _ _ _ member capOK
    exact ⟨z,zle.trans (by linarith),done⟩
