-- Prove2me | solution 1 for StableMSR.Recovery.RegionalSeeds.bounded_local_large_cluster_menus
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T13:18:43.192476+00:00
-- url     : https://prove2.me/submissions/23773d35-d04a-4bb0-abab-77d73453f1d1

import Theorems.Thm_StableMSR_Recovery_center_separation
import Theorems.Thm_StableMSR_Recovery_small_cluster_components
import Definitions.Def_StableMSR_RegionalSeeds
import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
open StableMSR.Recovery.RegionalSeeds
private lemma block_eq {n k : ℕ} {O : Partition n} (h : Feasible Finset.univ k O)
    {C D : Cluster n} (hc : C∈O) (hd : D∈O) {x : Point n} (hx : x∈C) (hy : x∈D) : C=D := by
  by_contra hn
  exact Finset.disjoint_left.mp (h.2.2.1 hc hd hn) hx hy
private lemma pointBlock {n k : ℕ} {O : Partition n} (h : Feasible Finset.univ k O)
    (x : Fin n) : ∃ C∈O, x∈C := by
  exact Finset.mem_biUnion.mp (h.2.2.2 ▸ Finset.mem_univ x)

private lemma clique {n : ℕ} (d : Point n → Point n → ℝ) (ds : ∀ x y, d x y=d y x)
    (t : ℝ) (C : Cluster n) (hc : C∈components d t Finset.univ)
    (x y : Fin n) (hx : x∈C) (hxy : d x y≤t) : y∈C := by
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hc
  have hr := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  by_cases heq : x=y
  · exact heq ▸ hr
  · exact hr.trans (SimpleGraph.Adj.reachable (G:=thresholdGraph d t Finset.univ)
      (show (thresholdGraph d t Finset.univ).Adj x y from
        ⟨heq,Finset.mem_univ _,Finset.mem_univ _,hxy,(ds x y) ▸ hxy⟩))


private lemma queryPt (x : World) (a b : Fin x.n) :
    MinSumFPT.oracleAnswer x.dist (a.val:ℤ) (b.val:ℤ)=x.dist a b := by
  simp [MinSumFPT.oracleAnswer,MinSumFPT.toPoint,a.isLt,b.isLt]
private lemma digitsFor {n : ℕ} (h : ℕ) (c w : ℕ→Fin n) :
    ∃u < rows n h, ∀j < h, digit n u (2*j)=(c j).val ∧ digit n u (2*j+1)=(w j).val := by
  let f (i : Fin (2*h)) := if i.val%2=0 then c (i.val/2) else w (i.val/2)
  let u : Fin (rows n h) := finFunctionFinEquiv f
  refine ⟨u.val,u.isLt,?_⟩
  intro j hj
  have atPos (i : Fin (2*h)) : digit n u.val i.val=(f i).val :=
    congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply f) i)
  exact ⟨by simpa [f] using atPos ⟨2*j,by omega⟩,
         by simpa [f,Nat.add_div] using atPos ⟨2*j+1,by omega⟩⟩
private lemma traceFeasible {n k : ℕ} {O : Partition n} (f : Feasible Finset.univ k O) (W : Cluster n) :
    Feasible W (tracePartition O W).card (tracePartition O W) := by
  classical
  refine ⟨rfl,?_,?_,?_⟩
  · intro A ha;obtain ⟨C,hc,rfl⟩:=Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hc).2
  · intro A ha B hb ne
    obtain ⟨C,hc,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨D,hd,rfl⟩:=Finset.mem_image.mp hb
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have eq:=block_eq f (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hd).1
      (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hq).1
    exact ne (by rw [eq])
  · ext p;constructor
    · intro h;obtain ⟨A,ha,hp⟩:=Finset.mem_biUnion.mp h
      obtain ⟨C,_,rfl⟩:=Finset.mem_image.mp ha
      exact (Finset.mem_inter.mp hp).2
    · intro hp;obtain ⟨C,hc,cp⟩:=pointBlock f p
      have hit : p∈C∩W := Finset.mem_inter.mpr ⟨cp,hp⟩
      exact Finset.mem_biUnion.mpr ⟨C∩W,Finset.mem_image.mpr ⟨C,Finset.mem_filter.mpr ⟨hc,⟨p,hit⟩⟩,rfl⟩,hit⟩
private lemma classesTrace {n k : ℕ} {O : Partition n} (f : Feasible Finset.univ k O) (W : Cluster n)
    (R : Relation) (match' : ∀p∈W,∀q∈W,R p.val q.val ↔ ∃C∈O,p∈C ∧ q∈C) :
    classes W R=tracePartition O W := by
  classical
  have slice {C : Cluster n} (hc : C∈O) {p : Fin n} (hp : p∈C) (pw : p∈W) :
      W.filter (fun q=>R p.val q.val)=C∩W := by
    ext q;simp only [Finset.mem_filter,Finset.mem_inter];constructor
    · rintro ⟨qw,adj⟩
      obtain ⟨D,hd,pd,qd⟩:=(match' p pw q qw).mp adj
      exact ⟨(block_eq f hd hc pd hp) ▸ qd,qw⟩
    · rintro ⟨qc,qw⟩;exact ⟨qw,(match' p pw q qw).mpr ⟨C,hc,hp,qc⟩⟩
  ext C;constructor
  · intro h;obtain ⟨p,pw,rfl⟩:=Finset.mem_image.mp h
    obtain ⟨D,hd,pd⟩:=pointBlock f p
    exact Finset.mem_image.mpr ⟨D,Finset.mem_filter.mpr ⟨hd,⟨p,Finset.mem_inter.mpr ⟨pd,pw⟩⟩⟩,(slice hd pd pw).symm⟩
  · intro h;obtain ⟨D,hd,rfl⟩:=Finset.mem_image.mp h
    obtain ⟨hd,⟨p,ph⟩⟩:=Finset.mem_filter.mp hd
    obtain ⟨pd,pw⟩:=Finset.mem_inter.mp ph
    exact Finset.mem_image.mpr ⟨p,pw,slice hd pd pw⟩
private lemma trace_aligned {n k : ℕ} {O : Partition n} (f : Feasible Finset.univ k O) (W : Cluster n)
    (al : Aligned O W) : tracePartition O W=restrictPartition O W := by
  obtain ⟨F,sub,un⟩:=al
  have whole {C : Cluster n} (hc : C∈O) (meet : (C∩W).Nonempty) : C⊆W := by
    obtain ⟨p,hp⟩:=meet
    obtain ⟨cp,pw⟩:=Finset.mem_inter.mp hp
    obtain ⟨D,hd,pd⟩:=Finset.mem_biUnion.mp (un.symm ▸ pw)
    have eq:=block_eq f hc (sub hd) cp pd
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
private lemma localSeed (x : World) (h : ℕ) (W : Cluster x.n) (hk : 1≤x.k) (hkn : x.k<x.n)
    (dmet : IsMetricArray x.dist) (e : ℝ) (he : 0<e) (hlt : e<1)
    (O : Partition x.n) (hs : Stable x.dist x.k (1+e) O) (hb : (meeting (largeClusters x.dist O e) W).card≤h) :
    ∃g≤h,∃u<rows x.n (h+1),∀p∈W,∀q∈W,
      digitRel (seedWorld x h) g u p.val q.val ↔ ∃C∈O,p∈C ∧ q∈C := by
  classical
  obtain ⟨metric,hm⟩ := dmet
  letI : MetricSpace (Point x.n) := metric
  have symmD (a b : Point x.n) : x.dist a b=x.dist b a := by simpa only [hm] using dist_comm a b
  have tri (a b c : Point x.n) : x.dist a c ≤ x.dist a b+x.dist b c := by simpa only [hm] using dist_triangle a b c
  let big := meeting (largeClusters x.dist O e) W
  let cut := smallThreshold x.dist O e
  have sub {C} (hC:C∈big) : C∈O := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).1
  have witnesses (C : ↥O) : ∃u v : Point x.n,C.val=ball x.dist u (x.dist u v) ∧
      x.dist u v=radius x.dist C.val ∧ ∀p∈C.val,x.dist u p≤radius x.dist C.val := by
    have ne := hs.1.2.1 C.val C.property
    obtain ⟨u,hu,eu⟩ := C.val.exists_mem_eq_inf' ne (eccentricity x.dist C.val)
    have er : radius x.dist C.val=eccentricity x.dist C.val u := by simpa [radius,ne] using eu
    have sep := (center_separation x.dist ⟨metric,hm⟩ x.k ⟨hk,hkn.le⟩ (1+e) (by linarith) O hs
      C.val C.property u ⟨hu,er.symm⟩).2.2.1
    obtain ⟨v,_,ev⟩ := C.val.exists_mem_eq_sup' ne (x.dist u)
    have eq : x.dist u v=radius x.dist C.val := by rw [er,eccentricity,dif_pos ne,ev]
    exact ⟨u,v,eq ▸ sep,eq,fun p hp=>by rw [er,eccentricity,dif_pos ne];exact Finset.le_sup' _ hp⟩
  choose ctr far shape price bound using witnesses
  have neO : O.Nonempty := Finset.card_pos.mp (by rw [hs.1.1];omega)
  obtain ⟨C₀,hC₀,maxC⟩ := O.exists_mem_eq_sup' neO (radius x.dist)
  have maxEq : largestRadius x.dist O=radius x.dist C₀ := by simpa [largestRadius,neO] using maxC
  have rad0 : 0 ≤ radius x.dist C₀ := by
    rw [←price ⟨C₀,hC₀⟩,←hm];exact dist_nonneg
  have cut0 : 0 ≤ cut := by
    dsimp [cut,smallThreshold];rw [maxEq];positivity
  let g:=big.card
  let E : Fin big.card ≃ ↥big := (Finset.equivFinOfCardEq (s:=big) rfl).symm
  let B (j : ℕ) : ↥O := if lt : j-1<big.card then
    ⟨(E ⟨j-1,lt⟩).val,sub (E ⟨j-1,lt⟩).property⟩ else ⟨C₀,hC₀⟩
  have activeBig (j : ℕ) (hv : 0<j ∧ j≤g) : (B j).val∈big := by
    have lt : j-1<big.card := by have a:=hv.1;have b : j≤big.card:=hv.2;omega
    simp only [B,dif_pos lt];exact (E ⟨j-1,lt⟩).property
  have listed (D : ↥big) : ∃j<h+1,0<j ∧ j≤g ∧ (B j).val=D.val := by
    let i:=E.symm D
    have hi : i.val<big.card:=i.isLt
    have bound' : big.card≤h:=hb
    refine ⟨i.val+1,by omega,by omega,by change i.val+1≤big.card;omega,?_⟩
    simpa [B,hi,i] using congrArg Subtype.val (E.apply_symm_apply D)
  let pairD (ab : Fin x.n × Fin x.n) := x.dist ab.1 ab.2
  let low := Finset.univ.filter (fun ab=>pairD ab ≤ 2*cut)
  let pt : Fin x.n := ⟨0,by omega⟩
  have neL : low.Nonempty := ⟨(pt,pt),Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
    dsimp [pairD];rw [←hm,dist_self];linarith⟩⟩
  obtain ⟨uv,huv,etop⟩ := low.exists_mem_eq_sup' neL pairD
  have threshold (p q : Point x.n) : x.dist p q ≤ x.dist uv.1 uv.2 ↔ x.dist p q ≤ 2*cut := by
    constructor
    · exact fun h=>h.trans ((Finset.mem_filter.mp huv).2)
    · intro hp;change pairD (p,q) ≤ pairD uv;rw [←etop]
      have mem : (p,q)∈low := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
      exact Finset.le_sup' pairD mem
  let c (j : ℕ) := if j=0 then uv.1 else ctr (B j)
  let w (j : ℕ) := if j=0 then uv.2 else far (B j)
  obtain ⟨u,hu,digits⟩ := digitsFor (h+1) c w
  let hit (v p : ℕ) := MinSumFPT.oracleAnswer x.dist (digit x.n u (2*v):ℤ) (p:ℤ) ≤
    MinSumFPT.oracleAnswer x.dist (digit x.n u (2*v):ℤ) (digit x.n u (2*v+1):ℤ)
  have hitsBlock (v : ℕ) (hv : 0<v ∧ v≤g) (p : Fin x.n) : hit v p.val ↔ p∈(B v).val := by
    dsimp [hit];rw [(digits v (by have a : g≤h:=hb;omega)).1,(digits v (by have a : g≤h:=hb;omega)).2,queryPt,queryPt]
    have vs : v≠0 := by omega
    change _ ↔ p∈(B v).val
    rw [shape (B v)];simp [c,w,vs,ball]
  have one (p : Fin x.n) : (∃v < h+1,(0<v ∧ v≤g) ∧ hit v p.val) ↔ ∃D∈big,p∈D := by
    constructor
    · rintro ⟨v,_,hv,hp⟩;exact ⟨_,activeBig v hv,(hitsBlock v hv p).mp hp⟩
    · rintro ⟨D,hD,hp⟩;obtain ⟨v,lt,pos,bnd,eq⟩ := listed ⟨D,hD⟩
      exact ⟨v,lt,⟨pos,bnd⟩,(hitsBlock v ⟨pos,bnd⟩ p).mpr (by simpa [eq] using hp)⟩
  have two (p q : Fin x.n) : (∃v < h+1,(0<v ∧ v≤g) ∧ hit v p.val ∧ hit v q.val) ↔ ∃D∈big,p∈D ∧ q∈D := by
    constructor
    · rintro ⟨v,_,hv,hp,hq⟩;exact ⟨_,activeBig v hv,(hitsBlock v hv p).mp hp,(hitsBlock v hv q).mp hq⟩
    · rintro ⟨D,hD,hp,hq⟩;obtain ⟨v,lt,pos,bnd,eq⟩ := listed ⟨D,hD⟩
      exact ⟨v,lt,⟨pos,bnd⟩,(hitsBlock v ⟨pos,bnd⟩ p).mpr (by simpa [eq] using hp),
        (hitsBlock v ⟨pos,bnd⟩ q).mpr (by simpa [eq] using hq)⟩
  have small := (small_cluster_components x.dist ⟨metric,hm⟩ x.k ⟨hk,hkn.le⟩ (1+e)
      ⟨by linarith,by linarith⟩ hkn O hs).1
  rw [show (1+e)-1=e by ring] at small
  refine ⟨g,hb,u,hu,?_⟩
  intro p pW q qW
  change ((∃v < h+1,(0<v ∧ v≤g) ∧ hit v p.val ∧ hit v q.val) ∨
    (¬∃v < h+1,(0<v ∧ v≤g) ∧ hit v p.val) ∧ (¬∃v < h+1,(0<v ∧ v≤g) ∧ hit v q.val) ∧
    distAt x p.val q.val ≤ MinSumFPT.oracleAnswer x.dist (digit x.n u (2*0):ℤ) (digit x.n u (2*0+1):ℤ)) ↔ _
  rw [two,one,one,distAt,queryPt,(digits 0 (by omega)).1,(digits 0 (by omega)).2,queryPt]
  simp only [c,w,if_true,threshold]
  constructor
  · rintro (⟨D,hD,hp,hq⟩|⟨np,_,near⟩)
    · exact ⟨D,sub hD,hp,hq⟩
    · obtain ⟨D,hD,hp⟩ := pointBlock hs.1 p
      have sm : D∈smallClusters x.dist O e := Finset.mem_filter.mpr ⟨hD,
        lt_of_not_ge (fun a=>np ⟨D,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hD,a⟩,⟨p,Finset.mem_inter.mpr ⟨hp,pW⟩⟩⟩,hp⟩)⟩
      exact ⟨D,hD,hp,clique x.dist symmD _ D (small D sm) p q hp near⟩
  · rintro ⟨D,hD,hp,hq⟩
    by_cases bg : D∈big
    · exact Or.inl ⟨D,bg,hp,hq⟩
    · have rad : radius x.dist D < cut := lt_of_not_ge (fun a=>bg (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hD,a⟩,⟨p,Finset.mem_inter.mpr ⟨hp,pW⟩⟩⟩))
      have outside (z : Fin x.n) (hz : z∈D) : ¬∃A∈big,z∈A := by
        rintro ⟨A,hA,ha⟩;exact bg ((block_eq hs.1 (sub hA) hD ha hz) ▸ hA)
      let A : ↥O := ⟨D,hD⟩
      refine Or.inr ⟨outside p hp,outside q hq,?_⟩
      have h1 : x.dist (ctr A) p ≤ radius x.dist D := bound A p hp
      have h2 : x.dist (ctr A) q ≤ radius x.dist D := bound A q hq
      have tr := tri p (ctr A) q
      rw [symmD p (ctr A)] at tr
      linarith

theorem solution (x : World) (h : ℕ) (W : Cluster x.n) (hk : 1≤x.k) (hn : x.k<x.n)
    (dm : IsMetricArray x.dist) :
    (RegionalSeeds.traceMenu x h W).card≤(h+1)*rows x.n (h+1) ∧
    (∀P∈RegionalSeeds.traceMenu x h W,Feasible W P.card P) ∧
    ∀(e : ℝ),0<e → e<1 → ∀O,Stable x.dist x.k (1+e) O →
      (meeting (largeClusters x.dist O e) W).card≤h →
      RegionalSeeds.tracePartition O W∈RegionalSeeds.traceMenu x h W ∧
      (Aligned O W → restrictPartition O W∈RegionalSeeds.traceMenu x h W) := by
  classical
  refine ⟨?_,?_,?_⟩
  · unfold traceMenu
    exact (Finset.card_filter_le ..).trans (Finset.card_image_le.trans (by simp))
  · intro P hp;exact (Finset.mem_filter.mp hp).2
  · intro e he hl O hs meeting'
    obtain ⟨g,hg,u,hu,eq⟩:=localSeed x h W hk hn dm e he hl O hs meeting'
    have out := classesTrace hs.1 W _ eq
    have belongs : tracePartition O W∈traceMenu x h W := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(g,u),?_,out⟩,traceFeasible hs.1 W⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr hu⟩
    exact ⟨belongs,fun a=>trace_aligned hs.1 W a ▸ belongs⟩

