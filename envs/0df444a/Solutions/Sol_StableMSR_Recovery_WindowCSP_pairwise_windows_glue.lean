-- Prove2me | solution 1 for StableMSR.Recovery.WindowCSP.pairwise_windows_glue
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T16:10:03.519147+00:00
-- url     : https://prove2.me/submissions/0fb9662c-c68d-44d6-9853-d130aa9934c2

import Theorems.Thm_StableMSR_Recovery_WindowCSP_greedy_anchor_covers
import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
theorem solution (x : World) (W : Cluster x.n) (R : ℝ) (h : ℕ) (P : Pick x.n)
    (dm : IsMetricArray x.dist) (hr : 0≤ R) (ok : valid x W R h P) :
    Feasible W (number x W R P) (WindowCSP.output x W R P) ∧
    cost x.dist (WindowCSP.output x W R P)=WindowCSP.price x W R P ∧
    WindowCSP.output x W R P=(greedyNet x.dist R W).biUnion (fun a=>accepted (anchor x.dist W R) a (P a)) := by
  classical
  let N:=greedyNet x.dist R W
  let own:=anchor x.dist W R
  let A (a : Point x.n):=accepted own a (P a)
  let D (a : Point x.n):=owned own a (P a)
  let U:=N.biUnion A
  obtain ⟨_,net⟩:=greedy_anchor_covers x.dist dm W R hr
  obtain ⟨metric,hm⟩:=dm
  letI : MetricSpace (Point x.n):=metric
  have sym (u v : Point x.n) : x.dist u v=x.dist v u := by simpa only [hm] using dist_comm u v
  have tri (u v w : Point x.n) : x.dist u w≤x.dist u v+x.dist v w := by simpa only [hm] using dist_triangle u v w
  have win {a : Point x.n} (ha : a∈N) :
      Feasible (window x.dist W R a) (P a).card (P a) := (Finset.mem_filter.mp (ok.1 a ha)).2
  have inside {a : Point x.n} (ha : a∈N) {C : Cluster x.n} (hc : C∈P a) : C⊆window x.dist W R a := by
    intro i hi;rw [←(win ha).2.2.2];exact Finset.mem_biUnion.mpr ⟨C,hc,hi⟩
  have inc {a : Point x.n} {C : Cluster x.n} (hc : C∈D a) : C∈A a := by
    obtain ⟨cp,i,hi,eq,_⟩:=Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨cp,i,hi,eq⟩
  have agree {a b : Point x.n} (ha : a∈N) (hb : b∈N) {C E : Cluster x.n}
      (hc : C∈A a) (hd : E∈A b) {i : Point x.n} (ci : i∈C) (di : i∈E) : C=E := by
    by_cases eq : a=b
    · subst b;by_contra ne
      exact Finset.disjoint_left.mp ((win ha).2.2.1 (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hd).1 ne) ci di
    · have b1:=(Finset.mem_inter.mp (inside ha (Finset.mem_filter.mp hc).1 ci)).2
      have b2:=(Finset.mem_inter.mp (inside hb (Finset.mem_filter.mp hd).1 di)).2
      have one:= (Finset.mem_filter.mp b1).2
      have two:= (Finset.mem_filter.mp b2).2
      change x.dist a i≤4*R at one
      change x.dist b i≤4*R at two
      have le : x.dist a b≤8*R := by have t:=tri a i b;rw [sym i b] at t;linarith
      have edge : (interactionGraph x.dist R W).Adj ⟨a,ha⟩ ⟨b,hb⟩ :=
        ⟨eq,ha,hb,le,by rw [sym];exact le⟩
      exact ok.2 ⟨a,ha⟩ ⟨b,hb⟩ edge C hc E hd ⟨i,Finset.mem_inter.mpr ⟨ci,di⟩⟩
  have atCore {i : Point x.n} (iw : i∈W) : ∃C∈A (own i),i∈C := by
    obtain ⟨ha,near⟩:=net i iw
    have mem : i∈window x.dist W R (own i) :=
      Finset.mem_inter.mpr ⟨iw,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp [own];linarith⟩⟩
    obtain ⟨C,cP,ci⟩:=Finset.mem_biUnion.mp ((win ha).2.2.2.symm ▸ mem)
    exact ⟨C,Finset.mem_filter.mpr ⟨cP,i,ci,rfl⟩,ci⟩
  have eqU : N.biUnion D=U := by
    ext C;constructor
    · intro ck;obtain ⟨a,ha,ca⟩:=Finset.mem_biUnion.mp ck
      exact Finset.mem_biUnion.mpr ⟨a,ha,inc ca⟩
    · intro ck;obtain ⟨a,ha,ca⟩:=Finset.mem_biUnion.mp ck
      let ne:=(win ha).2.1 C (Finset.mem_filter.mp ca).1
      let i:=C.min' ne
      have ci : i∈C:=C.min'_mem ne
      have iw:=(Finset.mem_inter.mp (inside ha (Finset.mem_filter.mp ca).1 ci)).1
      obtain ⟨E,ea,ei⟩:=atCore iw
      have ze:=agree ha (net _ iw).1 ca ea ci ei
      subst E
      exact Finset.mem_biUnion.mpr ⟨own i,(net _ iw).1,Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp ea).1,i,ci,rfl,fun j hj=>C.min'_le j hj⟩⟩
  have dis : (N : Set (Point x.n)).PairwiseDisjoint D := by
    intro a _ b _ ne
    apply Finset.disjoint_left.mpr;intro C ca cb
    obtain ⟨_,i,hi,ai,mi⟩:=Finset.mem_filter.mp ca
    obtain ⟨_,j,hj,bj,mj⟩:=Finset.mem_filter.mp cb
    exact ne (ai.symm.trans ((congrArg own (le_antisymm (mi j hj) (mj i hi))).trans bj))
  refine ⟨⟨Finset.card_biUnion dis,?_,?_,?_⟩,Finset.sum_biUnion dis,eqU⟩
  · intro C hc;obtain ⟨a,ha,cp⟩:=Finset.mem_biUnion.mp hc
    exact (win ha).2.1 _ (Finset.mem_filter.mp cp).1
  · intro C hc E he ne;obtain ⟨a,ha,ca⟩:=Finset.mem_biUnion.mp hc
    obtain ⟨b,hb,eb⟩:=Finset.mem_biUnion.mp he
    exact Finset.disjoint_left.mpr (fun _ ci ei=>ne (agree ha hb (inc ca) (inc eb) ci ei))
  · change (N.biUnion D).biUnion id=W;rw [eqU]
    ext i;constructor
    · intro mem;obtain ⟨C,cu,ci⟩:=Finset.mem_biUnion.mp mem
      obtain ⟨a,ha,ca⟩:=Finset.mem_biUnion.mp cu
      exact (Finset.mem_inter.mp (inside ha (Finset.mem_filter.mp ca).1 ci)).1
    · intro iw;obtain ⟨C,ca,ci⟩:=atCore iw
      exact Finset.mem_biUnion.mpr ⟨C,Finset.mem_biUnion.mpr ⟨own i,(net _ iw).1,ca⟩,ci⟩

