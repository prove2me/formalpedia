-- Prove2me | solution 1 for StableMSR.Recovery.FewBallRows.few_ball_seed_completeness
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T23:27:57.312685+00:00
-- url     : https://prove2.me/submissions/0aa4f9ed-6492-4c3c-965b-9bd90ddba906

import Theorems.Thm_StableMSR_Recovery_center_separation
import Theorems.Thm_StableMSR_Recovery_small_cluster_components
import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private lemma block_eq {n k : ℕ} {O : Partition n} (h : Feasible Finset.univ k O)
    {C D : Cluster n} (hc : C∈O) (hd : D∈O) {x : Point n} (hx : x∈C) (hy : x∈D) : C=D := by
  by_contra hn
  exact Finset.disjoint_left.mp (h.2.2.1 hc hd hn) hx hy
private lemma covers {n k : ℕ} {O : Partition n} (h : Feasible Finset.univ k O)
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
theorem solution (x : World) (h : ℕ) (hk : 1 ≤ x.k) (hkn : x.k < x.n) (hh : h < x.k)
    (dmet : IsMetricArray x.dist) (e : ℝ) (he : 0 < e) (hlt : e < 1)
    (O : Partition x.n) (hs : Stable x.dist x.k (1+e) O)
    (hb : (largeClusters x.dist O e).card ≤ h) :
    ∃u < rows x.n (h+1), FewBallRows.exact O (digitRel x h u) := by
  classical
  obtain ⟨metric,hm⟩ := dmet
  letI : MetricSpace (Point x.n) := metric
  have symmD (a b : Point x.n) : x.dist a b=x.dist b a := by simpa only [hm] using dist_comm a b
  have tri (a b c : Point x.n) : x.dist a c ≤ x.dist a b+x.dist b c := by simpa only [hm] using dist_triangle a b c
  let big := largeClusters x.dist O e
  let cut := smallThreshold x.dist O e
  have sub {C} (hC:C∈big) : C∈O := (Finset.mem_filter.mp hC).1
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
  have inBig : C₀∈big := by
    apply Finset.mem_filter.mpr
    refine ⟨hC₀,?_⟩
    unfold smallThreshold;rw [maxEq];nlinarith [mul_nonneg (sub_nonneg.mpr hlt.le) rad0]
  let base : ↥big := ⟨C₀,inBig⟩
  let E : Fin big.card ≃ ↥big := (Finset.equivFinOfCardEq (s:=big) rfl).symm
  let blk (j : ℕ) : ↥big := if lt : j-1<big.card then E ⟨j-1,lt⟩ else base
  let B (j : ℕ) : ↥O := ⟨(blk j).val,sub (blk j).property⟩
  have listed (D : ↥big) : ∃j < x.k,0<j ∧ j≤h ∧ blk j=D := by
    let i := E.symm D
    have hi : i.val < big.card := i.isLt
    have hb' : big.card≤h := hb
    refine ⟨i.val+1,by omega,by omega,by omega,?_⟩
    simpa [blk,hi,i] using E.apply_symm_apply D
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
  have hitsBlock (v : ℕ) (hv : 0<v ∧ v≤h) (p : Fin x.n) : hit v p.val ↔ p∈(blk v).val := by
    dsimp [hit];rw [(digits v (by omega)).1,(digits v (by omega)).2,queryPt,queryPt]
    have vs : v≠0 := by omega
    change _ ↔ p∈(B v).val
    rw [shape (B v)];simp [c,w,vs,ball]
  have one (p : Fin x.n) : (∃v < x.k,(0<v ∧ v≤h) ∧ hit v p.val) ↔ ∃D∈big,p∈D := by
    constructor
    · rintro ⟨v,_,hv,hp⟩;exact ⟨_,(blk v).property,(hitsBlock v hv p).mp hp⟩
    · rintro ⟨D,hD,hp⟩;obtain ⟨v,lt,pos,bnd,eq⟩ := listed ⟨D,hD⟩
      exact ⟨v,lt,⟨pos,bnd⟩,(hitsBlock v ⟨pos,bnd⟩ p).mpr (by simpa [eq] using hp)⟩
  have two (p q : Fin x.n) : (∃v < x.k,(0<v ∧ v≤h) ∧ hit v p.val ∧ hit v q.val) ↔ ∃D∈big,p∈D ∧ q∈D := by
    constructor
    · rintro ⟨v,_,hv,hp,hq⟩;exact ⟨_,(blk v).property,(hitsBlock v hv p).mp hp,(hitsBlock v hv q).mp hq⟩
    · rintro ⟨D,hD,hp,hq⟩;obtain ⟨v,lt,pos,bnd,eq⟩ := listed ⟨D,hD⟩
      exact ⟨v,lt,⟨pos,bnd⟩,(hitsBlock v ⟨pos,bnd⟩ p).mpr (by simpa [eq] using hp),
        (hitsBlock v ⟨pos,bnd⟩ q).mpr (by simpa [eq] using hq)⟩
  have small := (small_cluster_components x.dist ⟨metric,hm⟩ x.k ⟨hk,hkn.le⟩ (1+e)
      ⟨by linarith,by linarith⟩ hkn O hs).1
  rw [show (1+e)-1=e by ring] at small
  refine ⟨u,hu,?_⟩
  intro p q
  change ((∃v < x.k,(0<v ∧ v≤h) ∧ hit v p.val ∧ hit v q.val) ∨
    (¬∃v < x.k,(0<v ∧ v≤h) ∧ hit v p.val) ∧ (¬∃v < x.k,(0<v ∧ v≤h) ∧ hit v q.val) ∧
    distAt x p.val q.val ≤ MinSumFPT.oracleAnswer x.dist (digit x.n u (2*0):ℤ) (digit x.n u (2*0+1):ℤ)) ↔ _
  rw [two,one,one,distAt,queryPt,(digits 0 (by omega)).1,(digits 0 (by omega)).2,queryPt]
  simp only [c,w,if_true,threshold]
  constructor
  · rintro (⟨D,hD,hp,hq⟩|⟨np,_,near⟩)
    · exact ⟨D,sub hD,hp,hq⟩
    · obtain ⟨D,hD,hp⟩ := covers hs.1 p
      have sm : D∈smallClusters x.dist O e := Finset.mem_filter.mpr ⟨hD,
        lt_of_not_ge (fun a=>np ⟨D,Finset.mem_filter.mpr ⟨hD,a⟩,hp⟩)⟩
      exact ⟨D,hD,hp,clique x.dist symmD _ D (small D sm) p q hp near⟩
  · rintro ⟨D,hD,hp,hq⟩
    by_cases bg : D∈big
    · exact Or.inl ⟨D,bg,hp,hq⟩
    · have rad : radius x.dist D < cut := lt_of_not_ge (fun a=>bg (Finset.mem_filter.mpr ⟨hD,a⟩))
      have outside (z : Fin x.n) (hz : z∈D) : ¬∃A∈big,z∈A := by
        rintro ⟨A,hA,ha⟩;exact bg ((block_eq hs.1 (sub hA) hD ha hz) ▸ hA)
      let A : ↥O := ⟨D,hD⟩
      refine Or.inr ⟨outside p hp,outside q hq,?_⟩
      have h1 : x.dist (ctr A) p ≤ radius x.dist D := bound A p hp
      have h2 : x.dist (ctr A) q ≤ radius x.dist D := bound A q hq
      have tr := tri p (ctr A) q
      rw [symmD p (ctr A)] at tr
      linarith
