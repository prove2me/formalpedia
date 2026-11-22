-- Prove2me | solution 1 for StableMSR.Recovery.WindowCSP.stable_region_exact_table
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T16:11:19.578163+00:00
-- url     : https://prove2.me/submissions/7622db8a-8198-4644-a4c7-c661c7c38e1a

import Theorems.Thm_StableMSR_Recovery_WindowCSP_window_tree_plan
import Theorems.Thm_StableMSR_Recovery_WindowCSP_stable_window_representation
import Theorems.Thm_StableMSR_Recovery_WindowCSP_pairwise_windows_glue
import Theorems.Thm_StableMSR_Recovery_Supplement_local_treewidth
import Theorems.Thm_StableMSR_Recovery_optimum_restriction
import Definitions.Def_StableMSR_WindowPlans
import Definitions.Def_StableMSR_WindowCSP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
private lemma trace_aligned {n k : ℕ} {O : Partition n} (f : Feasible Finset.univ k O) (W : Cluster n)
    (al : Aligned O W) : tracePartition O W=restrictPartition O W := by
  obtain ⟨F,sub,un⟩:=al
  have whole {C : Cluster n} (hc : C∈O) (meet : (C∩W).Nonempty) : C⊆W := by
    obtain ⟨p,hp⟩:=meet
    obtain ⟨cp,pw⟩:=Finset.mem_inter.mp hp
    obtain ⟨D,hd,pd⟩:=Finset.mem_biUnion.mp (un.symm ▸ pw)
    have eq : C=D := by
      by_contra ne;exact Finset.disjoint_left.mp (f.2.2.1 hc (sub hd) ne) cp pd
    rw [eq,←un];intro q hq;exact Finset.mem_biUnion.mpr ⟨D,hd,hq⟩
  ext C;constructor
  · intro h;obtain ⟨D,hd,rfl⟩:=Finset.mem_image.mp h
    obtain ⟨hd,hD⟩:=Finset.mem_filter.mp hd
    have hw:=whole hd hD
    rw [Finset.inter_eq_left.mpr hw]
    exact Finset.mem_filter.mpr ⟨hd,hw⟩
  · intro h;obtain ⟨hc,hw⟩:=Finset.mem_filter.mp h
    have eq:=Finset.inter_eq_left.mpr hw
    exact Finset.mem_image.mpr ⟨C,Finset.mem_filter.mpr ⟨hc,eq.symm ▸ f.2.1 C hc⟩,eq⟩
private lemma volumeBound (x : World) (e : ℝ) (he : 0< e) (hl : e<1) (hk : 1≤ x.k) (hn : x.k< x.n) :
    (2*x.n+1)*((bagBound x (budget e) (widthBound e))^3*(x.k+1)^2)≤ x.n^(70*parameterEnvelope e) := by
  let n:=x.n
  let m:=budget e+1
  let t:=widthBound e+1
  let E:=parameterEnvelope e
  have two : 2≤ n:=by dsimp [n];omega
  have own : 1≤ ownerBound e := by
    unfold ownerBound;apply Nat.le_floor
    norm_num
    exact (le_div_iff₀ he).mpr (by linarith)
  have ltm : 0< m:=by dsimp [m];omega
  have lm : m≤5*ownerBound e:=by dsimp [m,budget];omega
  have prod : m*t≤5*E := by
    have le:=Nat.mul_le_mul_right t lm
    have major : ownerBound e*t≤ E:=by dsimp [t,E,parameterEnvelope];omega
    exact le.trans (by rw [Nat.mul_assoc];exact Nat.mul_le_mul_left 5 major)
  have base : m*n^(2*m)+1≤ n^(4*m) := by
    have a : m≤ n^m:=(Nat.lt_pow_self (by omega : 1< n)).le
    have g:=Nat.mul_le_mul_right (n^(2*m)) a
    rw [←Nat.pow_add,show m+2*m=3*m by omega] at g
    have one : 1≤ n^(3*m):=Nat.one_le_pow _ _ (by omega)
    have twice:=Nat.mul_le_mul_left (n^(3*m)) two
    calc
      _ ≤ n^(3*m)*n := by omega
      _ = n^(3*m+1) := (Nat.pow_succ ..).symm
      _ ≤ n^(4*m) := Nat.pow_le_pow_right (by omega) (by omega)
  have bag : bagBound x (budget e) (widthBound e)≤ n^(20*E) := by
    change (m*n^(2*m)+1)^t≤_
    apply (Nat.pow_le_pow_left base t).trans
    rw [←Nat.pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by rw [Nat.mul_assoc];omega)
  have c : x.k+1≤ n^2 := by
    have le:=Nat.mul_le_mul_right n two
    rw [pow_two]
    change x.k< n at hn;omega
  have g : 2*n+1≤ n^3 := by
    have a:=Nat.mul_le_mul_right n two
    have b:=Nat.mul_le_mul_right (n*n) two
    rw [pow_succ,pow_two]
    nlinarith
  have epos : 1≤ E:=by dsimp [E,parameterEnvelope];omega
  calc
    _ ≤ n^3*((n^(20*E))^3*(n^2)^2) :=
      Nat.mul_le_mul g (Nat.mul_le_mul (Nat.pow_le_pow_left bag 3) (Nat.pow_le_pow_left c 2))
    _ = n^(3+(20*E)*3+2*2) := by rw [←Nat.pow_mul,←Nat.pow_mul,←Nat.pow_add,←Nat.pow_add] <;> congr 1 <;> omega
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
theorem solution (x : World) (W : Cluster x.n) (e : ℝ) (he : 0< e) (hl : e<1)
    (hk : 1≤ x.k) (hn : x.k< x.n) (dm : IsMetricArray x.dist) (O : Partition x.n)
    (hs : Stable x.dist x.k (1+e) O) (hp : 0< largestRadius x.dist O)
    (ne : W.Nonempty) (al : Aligned O W) (small : diameter x.dist W≤ densityScale x.dist O e) :
    let R:=largestRadius x.dist O
    let J:=restrictPartition O W
    ∃p : TreeDP.Plan ↥(greedyNet x.dist R W) (Partition x.n),
      realizesWindows x W R (budget e) (widthBound e) p ∧
      p.rawCandidateVolume x.k≤ x.n^(70*parameterEnvelope e) ∧
      ∃u∈TreeDP.solve x.k p,∃Q : Pick x.n,valid x W R (budget e) Q ∧
        u.2.1=J.card ∧ number x W R Q=J.card ∧ WindowCSP.output x W R Q=J ∧
        WindowCSP.price x W R Q=cost x.dist J ∧ u.2.2=cost x.dist J := by
  classical
  let R:=largestRadius x.dist O
  let J:=restrictPartition O W
  let P : Pick x.n:=fun a=>tracePartition O (window x.dist W R a)
  obtain ⟨_,_,_,width⟩:=local_treewidth
  have ee : (1+e)-1=e:=by ring
  have tw:=width x.n x.k x.dist (1+e) O hk hn dm (by linarith) (by linarith) hs W al (by rwa [ee])
  rw [ee] at tw
  obtain ⟨p,realize⟩:=window_tree_plan x W R (budget e) (widthBound e) tw
  have vol:=(realize.2.2.2.2.1 x.k).2.trans (volumeBound x e he hl hk hn)
  obtain ⟨_,validP,outP⟩:=stable_window_representation x W e he hl hk hn dm O hs hp
  have trueOut : WindowCSP.output x W R P=J:=outP.trans (trace_aligned hs.1 W al)
  obtain ⟨fp,cp,_⟩:=pairwise_windows_glue x W R (budget e) P dm hp.le validP
  have numP : number x W R P=J.card:=fp.1.symm.trans (congrArg Finset.card trueOut)
  have costP : WindowCSP.price x W R P=cost x.dist J:=cp.symm.trans (congrArg (cost x.dist) trueOut)
  have count : J.card≤ x.k := (Finset.card_filter_le ..).trans_eq hs.1.1
  obtain ⟨u,hu,Q,uj,vQ,nQ,pQ,min⟩:=realize.2.2.2.2.2 x.k J.card count P validP numP
  obtain ⟨fq,cq,_⟩:=pairwise_windows_glue x W R (budget e) Q dm hp.le vQ
  rw [nQ] at fq
  have opt : UniqueOptimal x.dist Finset.univ x.k O := by
    apply hs.2
    obtain ⟨metric,hm⟩:=dm
    letI : MetricSpace (Point x.n):=metric
    refine ⟨fun a b=>by simpa only [hm] using dist_comm a b,?_⟩
    intro a b;have nonneg : 0≤ x.dist a b:=by rw [←hm];exact dist_nonneg
    exact ⟨le_rfl,by nlinarith [mul_nonneg he.le nonneg]⟩
  have loc:=optimum_restriction x.dist dm x.k ⟨hk,hn.le⟩ O opt W ne al
  have low:=loc.1.2 _ fq
  have high:=(min P validP numP).trans_eq costP
  have eqCost : cost x.dist (WindowCSP.output x W R Q)=cost x.dist J:=le_antisymm
    ((cq.trans pQ).le.trans high) low
  have equal : WindowCSP.output x W R Q=J:=loc.2 _ ⟨fq,fun other hother=>eqCost ▸ loc.1.2 other hother⟩
  exact ⟨p,realize,vol,u,hu,Q,vQ,uj,nQ,equal,cq.symm.trans eqCost,(cq.trans pQ).symm.trans eqCost⟩

