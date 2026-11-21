-- Prove2me | solution 1 for StableMSR.Recovery.FewBallRows.relation_ball_certificate
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T23:35:02.301668+00:00
-- url     : https://prove2.me/submissions/b8b1b824-8239-4237-b4fb-ee6fa23b03a3

import Definitions.Def_StableMSR_FewBallRows
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
private lemma getFirst (k : ℕ) (P : ℕ→Prop) (h : ∃j < k,P j) :
    ∃j < k,P j ∧ BallCoverCatalog.first k P=(j:ℤ) := by
  classical
  let z := Nat.find h
  have hz : z < k ∧ P z := Nat.find_spec h
  refine ⟨z,hz.1,hz.2,?_⟩
  have iff' (i : ℕ) (hi : i < k) : (P i ∧ ∀l < k,l < i → ¬P l) ↔ i=z := by
    constructor
    · rintro ⟨pi,lo⟩
      exact le_antisymm (le_of_not_gt (fun lt=>lo z hz.1 lt hz.2)) (Nat.find_min' h ⟨hi,pi⟩)
    · rintro rfl
      exact ⟨hz.2,fun l hl lt pl=>Nat.find_min h lt ⟨hl,pl⟩⟩
  unfold BallCoverCatalog.first
  calc
    _ = ∑i ∈ Finset.range k,if i=z then (i:ℤ) else 0 := Finset.sum_congr rfl (fun i hi=>by simp only [iff' i (Finset.mem_range.mp hi)])
    _ = _ := by simp [hz.1]
private lemma oracleFin {n : ℕ} (d : Point n→Point n→ℝ) (i j : Fin n) :
    MinSumFPT.oracleAnswer d (i.val:ℤ) (j.val:ℤ)=d i j := by
  simp [MinSumFPT.oracleAnswer,MinSumFPT.toPoint,i.isLt,j.isLt]
private lemma block_eq {n k : ℕ} {O : Partition n} (h : Feasible Finset.univ k O)
    {C D : Cluster n} (hc : C∈O) (hd : D∈O) {x : Point n} (hx : x∈C) (hy : x∈D) : C=D := by
  by_contra hn
  exact Finset.disjoint_left.mp (h.2.2.1 hc hd hn) hx hy
private lemma covers {n k : ℕ} {O : Partition n} (h : Feasible Finset.univ k O)
    (x : Fin n) : ∃ C∈O, x∈C := by
  exact Finset.mem_biUnion.mp (h.2.2.2 ▸ Finset.mem_univ x)

private lemma slots {n k : ℕ} (O : Partition n) (hf : Feasible Finset.univ k O)
    (R : Relation) (hr : FewBallRows.exact O R) : ∃E : Fin k ≃ ↥O,
    ∀j : Fin k,∀p : Fin n,slot n R j.val p.val ↔ p∈(E j).val := by
  classical
  let rep (B : ↥O) := B.val.min' (hf.2.1 B.val B.property)
  have rc (B : ↥O) : rep B∈B.val := Finset.min'_mem _ _
  have same (B : ↥O) (p : Fin n) (hp : p∈B.val) (q : Fin n) : R p.val q.val ↔ q∈B.val := by
    rw [hr p q];constructor
    · rintro ⟨C,hC,px,qx⟩
      exact (block_eq hf hC B.property px hp) ▸ qx
    · intro h;exact ⟨B.val,B.property,hp,h⟩
  have rootBlock (B : ↥O) (p : Fin n) (hp : p∈B.val) : root n R p.val ↔ p=rep B := by
    constructor
    · intro h;apply le_antisymm
      · exact h _ (rep B).isLt ((same B p hp _).mpr (rc B))
      · exact Finset.min'_le _ _ hp
    · rintro rfl q hq edge
      have h := (same B _ (rc B) ⟨q,hq⟩).mp edge
      exact Finset.min'_le _ _ h
  have inj : Function.Injective (fun B=> (rep B).val) := by
    intro B D e
    exact Subtype.ext (block_eq hf B.property D.property (rc B) ((Fin.ext e : rep B=rep D).symm ▸ rc D))
  let roots := (Finset.range n).filter (root n R)
  have rootMem (p : ℕ) : p∈roots ↔ ∃B : ↥O,(rep B).val=p := by
    constructor
    · intro hm;obtain ⟨hp,rt⟩ := Finset.mem_filter.mp hm
      let t : Fin n := ⟨p,Finset.mem_range.mp hp⟩
      obtain ⟨C,hC,hpC⟩ := covers hf t
      exact ⟨⟨C,hC⟩,congrArg Fin.val ((rootBlock ⟨C,hC⟩ t hpC).mp rt).symm⟩
    · rintro ⟨B,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (rep B).isLt,(rootBlock B _ (rc B)).mpr rfl⟩
  have rootsEq : roots=Finset.univ.image (fun B : ↥O=>(rep B).val) := by ext p;simp [rootMem]
  have num : roots.card=k := by rw [rootsEq,Finset.card_image_of_injective _ inj];simpa using hf.1
  have repmem (B : ↥O) : (rep B).val∈roots := (rootMem _).mpr ⟨_,rfl⟩
  have rk (p : ℕ) : rank n R p=(roots.filter (· < p)).card := by
    unfold rank;congr 1;ext q;simp [roots,and_left_comm,and_comm,and_assoc]
  have below (p : ℕ) (hp : p∈roots) : rank n R p<k := by
    rw [rk,←num];apply Finset.card_lt_card;apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _,?_⟩
    intro eq;have hm := eq.symm ▸ hp
    exact lt_irrefl p (Finset.mem_filter.mp hm).2
  have mono {p q : ℕ} (hp : p∈roots) (lt : p<q) : rank n R p < rank n R q := by
    rw [rk,rk];apply Finset.card_lt_card;apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨(fun i hi=>Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,lt_trans (Finset.mem_filter.mp hi).2 lt⟩),?_⟩
    intro eq
    have hm : p ∈ roots.filter (· < q) := Finset.mem_filter.mpr ⟨hp,lt⟩
    have impossible : p ∈ roots.filter (· < p) := eq.symm ▸ hm
    exact lt_irrefl p (show p < p from (Finset.mem_filter.mp impossible).2)
  let lab (B : ↥O) : Fin k := ⟨rank n R (rep B).val,below _ (repmem B)⟩
  have il : Function.Injective lab := by
    intro B D eq;apply inj
    have v : rank n R (rep B).val=rank n R (rep D).val := congrArg Fin.val eq
    rcases lt_trichotomy (rep B).val (rep D).val with l|e|l
    · exact False.elim ((ne_of_lt (mono (repmem B) l)) v)
    · exact e
    · exact False.elim ((ne_of_lt (mono (repmem D) l)) v.symm)
  have bij : Function.Bijective lab := (Fintype.bijective_iff_injective_and_card lab).2
    ⟨il,by simpa using hf.1⟩
  let L := Equiv.ofBijective lab bij
  refine ⟨L.symm,?_⟩
  intro j p
  have lj : lab (L.symm j)=j := L.apply_symm_apply j
  constructor
  · rintro ⟨v,hv,rt,rv,edge⟩
    let t : Fin n := ⟨v,hv⟩
    obtain ⟨C,hC,pc⟩ := covers hf t
    let B : ↥O := ⟨C,hC⟩
    have eq : t=rep B := (rootBlock B t pc).mp rt
    have bl : lab B=j := Fin.ext (by change rank n R (rep B).val=_;rw [←eq];exact rv)
    have sameB : B=L.symm j := il (bl.trans lj.symm)
    rw [←sameB];exact (same B t pc p).mp edge
  · intro hp
    let B := L.symm j
    exact ⟨_,(rep B).isLt,(rootBlock B _ (rc B)).mpr rfl,congrArg Fin.val lj,(same B _ (rc B) p).mpr hp⟩
private lemma validFirst (n : ℕ) (hn : 0<n) (p : ℕ→Prop) :
    ∃i : Fin n,first n p=(i.val:ℤ) := by
  classical
  by_cases h : ∃i<n,p i
  · obtain ⟨i,hi,_,eq⟩ := getFirst n p h;exact ⟨⟨i,hi⟩,eq⟩
  · refine ⟨⟨0,hn⟩,?_⟩
    unfold BallCoverCatalog.first;apply Finset.sum_eq_zero
    intro i hi;have np : ¬p i := fun hp=>h ⟨i,Finset.mem_range.mp hi,hp⟩
    simp [np]
theorem solution (x : World) (hn : 0 < x.n) (R : Relation) :
    (∀j,∃c w : Fin x.n,pickedCenter x R j=(c.val:ℤ) ∧ pickedWitness x R j=(w.val:ℤ)) ∧
    ∀(O : Partition x.n),Feasible Finset.univ x.k O → FewBallRows.exact O R →
    ∀(m : ℕ→ℤ) (r : ℕ),encoded x (withMem x m) r R →
      good (withMem x m) r ∧ score (withMem x m) r=cost x.dist O := by
  classical
  constructor
  · intro j
    obtain ⟨c,hc⟩ := validFirst x.n hn (fun c=>∃w<x.n,best x R j c w)
    obtain ⟨w,hw⟩ := validFirst x.n hn (fun w=>best x R j (pickedCenter x R j).toNat w)
    exact ⟨c,w,hc,hw⟩
  intro O hf hr m r write
  obtain ⟨E,members⟩ := slots O hf R hr
  let B (j : Fin x.k) := (E j).val
  have val (a b : Fin x.n) : distAt x a.val b.val=x.dist a b := oracleFin x.dist a b
  have certified (j : Fin x.k) : ∃c w : Fin x.n,c∈B j ∧
      pickedCenter x R j.val=(c.val:ℤ) ∧ pickedWitness x R j.val=(w.val:ℤ) ∧
      x.dist c w=radius x.dist (B j) ∧ ∀p∈B j,x.dist c p ≤ x.dist c w := by
    let K := B j
    have ne : K.Nonempty := hf.2.1 _ (E j).property
    obtain ⟨u,hu,eu⟩ := K.exists_mem_eq_inf' ne (eccentricity x.dist K)
    obtain ⟨v,hv,ev⟩ := K.exists_mem_eq_sup' ne (x.dist u)
    have euv : x.dist u v=radius x.dist K := by rw [radius,dif_pos ne,eu,eccentricity,dif_pos ne,ev]
    have covers' (c w : Fin x.n) : encloses x R j c.val w.val ↔
        c∈K ∧ w∈K ∧ ∀p∈K,x.dist c p ≤ x.dist c w := by
      unfold encloses;rw [members j c,members j w]
      apply and_congr_right;intro _;apply and_congr_right;intro _
      constructor
      · intro h p hp;simpa only [val] using h p.val p.isLt ((members j p).mpr hp)
      · intro h i hi si;let p : Fin x.n := ⟨i,hi⟩;exact (val c p).symm ▸ (val c w).symm ▸ h p ((members j p).mp si)
    have lower (c w : Fin x.n) (hw : encloses x R j c.val w.val) : radius x.dist K ≤ x.dist c w := by
      obtain ⟨hc,_,bound⟩ := (covers' c w).mp hw
      rw [radius,dif_pos ne]
      apply (Finset.inf'_le _ hc).trans
      rw [eccentricity,dif_pos ne];exact Finset.sup'_le _ _ bound
    have encUV : encloses x R j u.val v.val := (covers' u v).mpr
      ⟨hu,hv,fun p hp=>by rw [←ev];exact Finset.le_sup' _ hp⟩
    have optUV : best x R j u.val v.val := by
      refine ⟨encUV,?_⟩;intro a ha b hb enc
      let a' : Fin x.n := ⟨a,ha⟩;let b' : Fin x.n := ⟨b,hb⟩
      calc distAt x u.val v.val = radius x.dist K := (val u v).trans euv
           _ ≤ x.dist a' b' := lower a' b' enc
           _ = _ := (val a' b').symm
    obtain ⟨c,hc,hw,ec⟩ := getFirst x.n (fun a=>∃b<x.n,best x R j a b)
      ⟨u.val,u.isLt,v.val,v.isLt,optUV⟩
    have eqC : pickedCenter x R j=(c:ℤ) := ec
    obtain ⟨ww,hww,ow⟩ := hw
    have exW : ∃b<x.n,best x R j (pickedCenter x R j).toNat b := by simpa [eqC] using (show ∃b<x.n,best x R j c b from ⟨ww,hww,ow⟩)
    obtain ⟨w,hw,ow,ew⟩ := getFirst _ _ exW
    let c' : Fin x.n := ⟨c,hc⟩;let w' : Fin x.n := ⟨w,hw⟩
    have opt : best x R j c'.val w'.val := by simpa [eqC] using ow
    have uv := opt.2 u.val u.isLt v.val v.isLt encUV
    have le : x.dist c' w' ≤ radius x.dist K := by simpa only [val,euv] using uv
    exact ⟨c',w',((covers' c' w').mp opt.1).1,eqC,ew,le_antisymm le (lower c' w' opt.1),((covers' c' w').mp opt.1).2.2⟩
  choose c w inside cc ww rad cover using certified
  let y := withMem x m
  have C (j : Fin x.k) : center y r j.val=((c j).val:ℤ) := (write j j.isLt).1.trans (cc j)
  have W (j : Fin x.k) : witness y r j.val=((w j).val:ℤ) := (write j j.isLt).2.trans (ww j)
  have price (j : Fin x.k) : charge y r j.val=radius x.dist (B j) := by
    rw [charge,C,W];exact (oracleFin x.dist (c j) (w j)).trans (rad j)
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro j hj l hl eq
    let a : Fin x.k := ⟨j,hj⟩;let b : Fin x.k := ⟨l,hl⟩
    have v : c a=c b := Fin.ext (Int.ofNat.inj ((C a).symm.trans (eq.trans (C b))))
    have blocks : B a=B b := block_eq hf (E a).property (E b).property (inside a) (v.symm ▸ inside b)
    exact congrArg Fin.val (E.injective (Subtype.ext blocks))
  · intro i hi
    let p : Fin x.n := ⟨i,hi⟩
    obtain ⟨D,hD,hm⟩ := covers hf p
    let j := E.symm ⟨D,hD⟩
    have eq : B j=D := congrArg Subtype.val (E.apply_symm_apply ⟨D,hD⟩)
    refine ⟨j.val,j.isLt,?_⟩
    change MinSumFPT.oracleAnswer y.dist (center y r j.val) (p.val:ℤ) ≤ charge y r j.val
    rw [C,charge,C,W];change distAt x (c j).val p.val ≤ distAt x (c j).val (w j).val
    rw [val,val];exact cover j p (eq ▸ hm)
  · calc
      score y r = ∑j : Fin x.k,charge y r j.val := (Fin.sum_univ_eq_sum_range _ _).symm
      _ = ∑j : Fin x.k,radius x.dist (B j) := Finset.sum_congr rfl (fun j _=>price j)
      _ = ∑K : O,radius x.dist K.val := E.sum_comp (fun K=>radius x.dist K.val)
      _ = cost x.dist O := Finset.sum_attach _ _
