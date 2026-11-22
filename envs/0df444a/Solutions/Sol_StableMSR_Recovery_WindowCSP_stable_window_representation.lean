-- Prove2me | solution 1 for StableMSR.Recovery.WindowCSP.stable_window_representation
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T16:10:21.256191+00:00
-- url     : https://prove2.me/submissions/e56c6d9a-5e1a-492f-afa5-a59281b1a797

import Theorems.Thm_StableMSR_Recovery_WindowCSP_greedy_anchor_covers
import Theorems.Thm_StableMSR_Recovery_WindowCSP_pairwise_windows_glue
import Theorems.Thm_StableMSR_Recovery_local_cluster_density
import Theorems.Thm_StableMSR_Recovery_RegionalSeeds_bounded_local_large_cluster_menus
import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
theorem solution (x : World) (W : Cluster x.n) (e : ℝ) (he : 0< e) (hl : e<1)
    (hk : 1≤ x.k) (hn : x.k< x.n) (dm : IsMetricArray x.dist) (O : Partition x.n)
    (hs : Stable x.dist x.k (1+e) O) (hp : 0< largestRadius x.dist O) :
    let R:=largestRadius x.dist O
    let P : Pick x.n :=fun a=>tracePartition O (window x.dist W R a)
    (∀a : Point x.n,(meeting (largeClusters x.dist O e) (window x.dist W R a)).card≤ budget e ∧
      (traceMenu x (budget e) (window x.dist W R a)).card≤(budget e+1)*CartesianBallRows.rows x.n (budget e+1)) ∧
    valid x W R (budget e) P ∧ WindowCSP.output x W R P=tracePartition O W := by
  classical
  let R:=largestRadius x.dist O
  let P : Pick x.n:=fun a=>tracePartition O (window x.dist W R a)
  let own:=anchor x.dist W R
  let N:=greedyNet x.dist R W
  have gt : 0<R:=hp
  have pars : 1<1+e ∧ 1+e<2:=⟨by linarith,by linarith⟩
  have den:=(local_cluster_density x.dist dm x.k ⟨hk,hn.le⟩ (1+e) pars hn O hs).2.2
  rw [show 1+e-1=e by ring] at den
  have bound (a : Point x.n) : (meeting (largeClusters x.dist O e) (window x.dist W R a)).card≤budget e := by
    have ss : meeting (largeClusters x.dist O e) (window x.dist W R a) ⊆
        meeting (largeClusters x.dist O e) (ball x.dist a (4*R)) := by
      intro D hD;obtain ⟨dD,i,hi⟩:=Finset.mem_filter.mp hD
      obtain ⟨di,win⟩:=Finset.mem_inter.mp hi
      exact Finset.mem_filter.mpr ⟨dD,i,Finset.mem_inter.mpr ⟨di,(Finset.mem_inter.mp win).2⟩⟩
    have d:=den a (4*R) (by positivity)
    have ratio : (4*R+2*largestRadius x.dist O)/smallThreshold x.dist O e=2*(12/e) := by
      change (4*R+2*R)/(e*R/4)=_;field_simp;ring
    rw [ratio] at d
    have up : (12/e)<(ownerBound e:ℝ)+1:=Nat.lt_floor_add_one _
    have le:=Finset.card_le_card ss
    have comp : ((meeting (largeClusters x.dist O e) (window x.dist W R a)).card:ℝ)≤(budget e:ℝ) := by
      unfold budget;push_cast
      have cast : ((meeting (largeClusters x.dist O e) (window x.dist W R a)).card:ℝ)≤
          ((meeting (largeClusters x.dist O e) (ball x.dist a (4*R))).card:ℝ) := by exact_mod_cast le
      linarith
    exact_mod_cast comp
  have menus (a : Point x.n) := bounded_local_large_cluster_menus x (budget e) (window x.dist W R a) hk hn dm
  obtain ⟨_,net⟩:=greedy_anchor_covers x.dist dm W R gt.le
  obtain ⟨metric,hm⟩:=dm
  letI : MetricSpace (Point x.n):=metric
  have tri (a b c : Point x.n) : x.dist a c≤x.dist a b+x.dist b c := by simpa only [hm] using dist_triangle a b c
  have diam {D : Cluster x.n} (hd : D∈O) {i j : Point x.n} (hi : i∈D) (hj : j∈D) : x.dist i j≤2*R := by
    have ne:=hs.1.2.1 D hd
    obtain ⟨z,hz,zmin⟩:=D.exists_mem_eq_inf' ne (eccentricity x.dist D)
    have eq : radius x.dist D=eccentricity x.dist D z := by simpa [radius,ne] using zmin
    have Opos : O.Nonempty:=⟨D,hd⟩
    have top : radius x.dist D≤R := by
      dsimp [R,largestRadius];rw [dif_pos Opos];exact Finset.le_sup' _ hd
    have rad (q : Point x.n) (hq : q∈D) : x.dist z q≤radius x.dist D := by
      rw [eq,eccentricity,dif_pos ne];exact Finset.le_sup' _ hq
    have t:=tri i z j
    have eqd : x.dist i z=x.dist z i := by simpa only [hm] using dist_comm i z
    rw [eqd] at t;linarith [rad i hi,rad j hj]
  have full {D : Cluster x.n} (hd : D∈O) {i a : Point x.n} (hi : i∈D) (iw : i∈W) (ha : own i=a) :
      D∩window x.dist W R a=D∩W := by
    ext j;constructor
    · intro h;obtain ⟨jd,jw⟩:=Finset.mem_inter.mp h
      exact Finset.mem_inter.mpr ⟨jd,(Finset.mem_inter.mp jw).1⟩
    · intro h;obtain ⟨jd,jw⟩:=Finset.mem_inter.mp h
      have near : x.dist a i≤2*R:=ha ▸ (net _ iw).2
      exact Finset.mem_inter.mpr ⟨jd,Finset.mem_inter.mpr ⟨jw,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,by linarith [tri a i j,diam hd hi jd]⟩⟩⟩
  have active {a : Point x.n} {C : Cluster x.n} (hc : C∈accepted own a (P a)) :
      ∃D∈O,C=D∩W ∧ C.Nonempty := by
    obtain ⟨cp,i,ci,io⟩:=Finset.mem_filter.mp hc
    obtain ⟨D,df,rfl⟩:=Finset.mem_image.mp cp
    obtain ⟨di,iw⟩:=Finset.mem_inter.mp ci
    have hd:=(Finset.mem_filter.mp df).1
    exact ⟨D,hd,full hd di (Finset.mem_inter.mp iw).1 io,⟨i,ci⟩⟩
  have ok : valid x W R (budget e) P := by
    refine ⟨fun a _=>((menus a).2.2 e he hl O hs (bound a)).1,?_⟩
    intro a b _ C hc E he'
    obtain ⟨D,hd,dC,_⟩:=active hc
    obtain ⟨F,hf,fE,_⟩:=active he'
    rintro ⟨i,hit⟩;obtain ⟨ic,ie⟩:=Finset.mem_inter.mp hit
    rw [dC] at ic;rw [fE] at ie
    have eq : D=F := by
      by_contra ne
      exact Finset.disjoint_left.mp (hs.1.2.2.1 hd hf ne) (Finset.mem_inter.mp ic).1 (Finset.mem_inter.mp ie).1
    rw [dC,fE,eq]
  refine ⟨fun a=>⟨bound a,(menus a).1⟩,ok,?_⟩
  rw [(pairwise_windows_glue x W R (budget e) P ⟨metric,hm⟩ gt.le ok).2.2]
  ext C;constructor
  · intro h;obtain ⟨a,_,ca⟩:=Finset.mem_biUnion.mp h
    obtain ⟨D,hd,eq,ne⟩:=active ca
    exact Finset.mem_image.mpr ⟨D,Finset.mem_filter.mpr ⟨hd,eq ▸ ne⟩,eq.symm⟩
  · intro h;obtain ⟨D,df,rfl⟩:=Finset.mem_image.mp h
    obtain ⟨hd,i,ih⟩:=Finset.mem_filter.mp df
    obtain ⟨di,iw⟩:=Finset.mem_inter.mp ih
    let a:=own i
    have eq:=full hd di iw (a:=a) rfl
    have ne : (D∩window x.dist W R a).Nonempty := eq.symm ▸ (show (D∩W).Nonempty from ⟨i,ih⟩)
    have cp : D∩W∈P a:=Finset.mem_image.mpr ⟨D,Finset.mem_filter.mpr ⟨hd,ne⟩,eq⟩
    exact Finset.mem_biUnion.mpr ⟨a,(net i iw).1,Finset.mem_filter.mpr ⟨cp,i,ih,rfl⟩⟩

