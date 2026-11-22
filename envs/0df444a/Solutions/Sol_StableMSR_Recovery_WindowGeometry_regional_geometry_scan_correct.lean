-- Prove2me | solution 1 for StableMSR.Recovery.WindowGeometry.regional_geometry_scan_correct
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:31:59.832142+00:00
-- url     : https://prove2.me/submissions/2ec181d5-c452-49b2-8d5e-103e22b0bf3e

import Definitions.Def_StableMSR_RegionAtlas
import Theorems.Thm_StableMSR_Recovery_WindowGeometry_canonical_net_prefix
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowGeometry
private lemma splitRadix {n a i : ℕ} (h : i< n) : (a*n+i)/n=a ∧ (a*n+i)%n=i:=by
  have pos : 0< n:=by omega
  constructor
  · rw [Nat.mul_comm a n,Nat.mul_add_div pos,Nat.div_eq_of_lt h,Nat.add_zero]
  · simp [Nat.add_mod,Nat.mod_eq_of_lt h]
private lemma unticket {n q a b : ℕ} (ha : a< n) (hb : b< n) :
    sourceRow n (ticket n q a b)=q ∧ firstCount n (ticket n q a b)=a ∧ lastCount n (ticket n q a b)=b:=by
  have e : ticket n q a b-1=(q*n+a)*n+b:=by unfold ticket;omega
  have t:=splitRadix (a:=q*n+a) hb;have u:=splitRadix (a:=q) ha
  simp only [sourceRow,firstCount,lastCount,e,t.1,t.2,u.1,u.2,and_self]
private lemma nextDigit {n a b i : ℕ} (hi : i< n) (h : a< b) (j : ℕ) : a*n+i< b*n+j:=by
  have one : a*n+i<(a+1)*n:=by rw [Nat.succ_mul];omega
  exact one.trans_le ((Nat.mul_le_mul_right n h).trans (Nat.le_add_right ..))
private lemma shortTicket {n q a b m : ℕ} (hq : q< m) (ha : a< n) (hb : b< n) : ticket n q a b< volume m n:=by
  have one:=nextDigit ha hq 0;have two:=nextDigit hb (show q*n+a< m*n by omega) 0
  unfold ticket volume;omega
private lemma ticketPos (n q a b : ℕ) : 0< ticket n q a b:=by unfold ticket;omega
private lemma subAt (x : World) (p d : ℕ) (hd : d< x.rows) : subR x (p+d) p=d:=by
  classical
  unfold subR;rw [Finset.sum_eq_single d]
  · simp
  · intro b _ ne;exact if_neg (by omega)
  · intro h;exact (h (Finset.mem_range.mpr hd)).elim
private lemma subSmall (x : World) (a b : ℕ) (ha : a< x.rows) : subR x a b=a-b:=by
  by_cases h : b≤ a
  · have eq:=subAt x b (a-b) (by omega);rwa [show b+(a-b)=a by omega] at eq
  · unfold subR;rw [Finset.sum_eq_zero (fun i _=>if_neg (by omega)),Nat.sub_eq_zero_of_le (by omega)]
private lemma divAt (x : World) (p d : ℕ) (hp : p< x.rows) (hd : d< x.n) : divN x (p*x.n+d)=p:=by
  classical
  unfold divN;rw [Finset.sum_eq_single p]
  · exact if_pos ⟨by omega,by rw [Nat.succ_mul];omega⟩
  · intro b _ ne;apply if_neg;intro h
    rcases lt_or_gt_of_ne ne with less|more
    · have q:=Nat.mul_le_mul_right x.n (show b+1≤ p from less);omega
    · have q:=nextDigit hd more 0;omega
  · intro h;exact (h (Finset.mem_range.mpr hp)).elim
private lemma remAt (x : World) (p d : ℕ) (hp : p< x.rows) (hd : d< x.n) (dr : d< x.rows) :
    remN x (p*x.n+d)=d:=by rw [remN,divAt x p d hp hd,subAt _ _ _ dr]
open StableMSR.Recovery.Supplement
private lemma finDist (x : World) (a b : Point x.n) : FewBallRows.distAt x a.val b.val=x.dist a b:=by
  simp [FewBallRows.distAt,MinSumFPT.oracleAnswer,MinSumFPT.toPoint,a.isLt,b.isLt]
private lemma subsetNet {n : ℕ} (d : Point n→Point n→ℝ) (R : ℝ) (W : Cluster n) : greedyNet d R W⊆W:=by
  let step (S : Cluster n) (p : Point n):=if ∀a∈S,2*R< d p a then insert p S else S
  have work (L : List (Point n)) (A : Cluster n) (h : A⊆W) (all : ∀p∈L,p∈W) : L.foldl step A⊆W:=by
    induction L generalizing A with
    | nil=>exact h
    | cons p L ih=>
      apply ih _ _ (fun p hp=>all p (List.mem_cons_of_mem _ hp))
      dsimp [step];split
      · exact Finset.insert_subset (all p (List.mem_cons_self ..)) h
      · exact h
  exact work (W.sort (·≤·)) ∅ (Finset.empty_subset _) (fun p hp=>Finset.mem_sort _ |>.mp hp)
private lemma keyCorrect {n : ℕ} (d : Point n→Point n→ℝ) (R : ℝ) (W : Cluster n)
    (x : World) (i : Point n) (size : x.n=n)
    (ds : ∀a : Point n,FewBallRows.distAt x a.val i.val=d a i)
    (sc : unitR x=R) (sel : ∀a : Point n,selected x a.val ↔ a∈greedyNet d R W) :
    nearestKey x i.val=((anchor d W R i).val:ℤ):=by
  classical
  let N:=greedyNet d R W
  let S:=N.filter (fun a=>d a i≤2*R)
  let P (a : ℕ):=selected x a ∧ FewBallRows.distAt x a i.val≤2*unitR x
  have elem (a : Point n) : P a.val ↔ a∈S:=by simp [P,S,N,ds,sel,sc]
  have test : (∃a< x.n,P a) ↔ S.Nonempty:=by
    constructor
    · rintro ⟨a,lo,yes⟩;let t : Point n:=⟨a,size ▸ lo⟩;exact ⟨t,(elem t).mp yes⟩
    · rintro ⟨a,yes⟩;exact ⟨a.val,size.symm ▸ a.isLt,(elem a).mpr yes⟩
  change (if ∃a< x.n,P a then first x.n P else (i.val:ℤ))=((Supplement.representative S i).val:ℤ)
  by_cases ne : S.Nonempty
  · let a:=S.min' ne
    have inS : a∈S:=S.min'_mem ne
    have good : P a.val:=(elem a).mpr inS
    have least (b : ℕ) (bl : b< x.n) (pb : P b) : a.val≤ b:=
      S.min'_le ⟨b,size ▸ bl⟩ ((elem _).mp pb)
    rw [if_pos (test.mpr ne)];unfold Supplement.representative;rw [dif_pos ne]
    unfold first;rw [Finset.sum_eq_single a.val]
    · exact if_pos ⟨good,fun b bl ba pb=>by have:=least b bl pb;omega⟩
    · intro b hb no;apply if_neg;rintro ⟨pb,prev⟩
      have l:=least b (Finset.mem_range.mp hb) pb
      exact prev a.val (size.symm ▸ a.isLt) (by omega) good
    · intro no;exact (no (Finset.mem_range.mpr (size.symm ▸ a.isLt))).elim
  · rw [if_neg (fun h=>ne (test.mp h))];simp [Supplement.representative,ne]
theorem solution (x : World) (hk : 0< x.k) (space : 2+x.n+x.n*x.n≤ x.rows)
    (h : ℕ→WindowProfiles.Mem) (m : WindowProfiles.Mem)
    (start : Writes x (WindowProfiles.replace x (h 0)) reset)
    (steps : ∀i< x.rows,Writes (WindowProfiles.replace x (h i)) (WindowProfiles.replace x (h (i+1))) sweep)
    (endpass : Writes (WindowProfiles.replace x (h x.rows)) (WindowProfiles.replace x m) expose) : Atlas x m := by
  classical
  let X (t : ℕ):=WindowProfiles.replace x (h t)
  let out:=WindowProfiles.replace x m
  let W:=region x;let R:=unitR x
  let U (t : ℕ):=W.filter (fun p=>p.val< t)
  let N (t : ℕ):=greedyNet x.dist R (U t)
  have lo : 1< x.rows:=by omega
  have pt (p : Point x.n) : 2+p.val< x.rows:=by have:=p.isLt;omega
  have initN : N 0=∅:=by simp [N,U,greedyNet]
  have inv (t : ℕ) (ht : t≤ x.rows) :
      witness (X t) 0 0=(t:ℤ) ∧
      (∀r< x.rows,center (X t) r 0=center x r 0) ∧
      ∀p : Point x.n,selected (X t) p.val ↔ p∈N t:=by
    induction t with
    | zero =>
      have clk:=start 0 (by omega) 0 hk true
      refine ⟨by simpa [reset,field,X] using clk,?_,?_⟩
      · intro r hr;simpa [reset,field,X] using start r hr 0 hk false
      · intro p;have atp:=start (2+p.val) (pt p) 0 hk true
        have limit : 2+p.val<2+x.n:=by have:=p.isLt;omega
        simp [reset,limit,field] at atp
        change 0< witness (X 0) (2+p.val) 0 ↔ _;rw [initN,atp];simp
    | succ t ih=>
      have tl : t< x.rows:=by omega
      obtain ⟨clk,old,sel⟩:=ih (by omega)
      have clk' : (witness (X t) 0 0).toNat=t:=by rw [clk];simp
      have advance (r : ℕ) (hr : r< x.rows) (s : Bool) :
          field (X (t+1)) r 0 s=sweep (X t) r 0 s:=steps t tl r hr 0 hk s
      have sc : unitR (X t)=R:=by unfold unitR R;rw [old 0 (by omega),old 1 lo];rfl
      have insideEq (p : Point x.n) : inside (X t) p.val ↔ p∈W:=by
        change 0< center _ (2+p.val) 0 ↔ p∈Finset.univ.filter (fun q : Point x.n=>inside x q.val)
        rw [Finset.mem_filter,old _ (pt p)];simp [inside]
      refine ⟨?_,?_,?_⟩
      · have up:=advance 0 (by omega) true
        simpa [sweep,field,clk] using up
      · intro r hr;exact (show center (X (t+1)) r 0=center (X t) r 0 from by simpa [sweep,field] using advance r hr false).trans (old _ hr)
      · intro p
        have step:=advance (2+p.val) (pt p) true
        have nz : 2+p.val≠0:=by omega
        change witness (X (t+1)) (2+p.val) 0=sweep (X t) (2+p.val) 0 true at step
        simp [sweep,clk',nz,show (X t).n=x.n from rfl,field] at step
        change (0< witness (X (t+1)) (2+p.val) 0) ↔ _
        by_cases time : t< x.n
        · let q : Point x.n:=⟨t,time⟩
          have net:=canonical_net_prefix x.dist R W q
          change N (t+1)=(if q∈W ∧ ∀s∈N t,2*R< x.dist q s then insert q (N t) else N t) at net
          have ad : admitPoint (X t) t ↔ q∈W ∧ ∀s∈N t,2*R< x.dist q s:=by
            unfold admitPoint;rw [show inside (X t) t ↔ q∈W from insideEq q,sc];apply and_congr_right;intro _
            constructor
            · intro test a ha;have h:=test a.val a.isLt ((sel a).mpr ha)
              change 2*R< FewBallRows.distAt x q.val a.val at h;simpa only [finDist] using h
            · intro test v hv sv;let a : Point x.n:=⟨v,hv⟩
              change 2*R< FewBallRows.distAt x q.val a.val;rw [finDist];exact test a ((sel a).mp sv)
          by_cases eq : p=q
          · subst p
            have oldno : q∉N t:=fun h=>by have h':= (Finset.mem_filter.mp (subsetNet x.dist R (U t) h)).2;change t< t at h';omega
            have current : witness (X (t+1)) (2+q.val) 0=(if admitPoint (X t) t then 1 else 0):=by simpa [q,time] using step
            rw [current,net];by_cases yes : admitPoint (X t) t
            · rw [if_pos yes,if_pos (ad.mp yes)];simp
            · rw [if_neg yes,if_neg (mt ad.mpr yes)];simp [oldno]
          · have pe : p.val≠t:=fun v=>eq (Fin.ext v)
            have addr : 2+p.val≠2+t:=by omega
            simp only [pe,false_and,if_false] at step;rw [step,net]
            change selected (X t) p.val ↔ _
            split <;> simp [eq,sel p]
        · have ue : U (t+1)=U t:=by
            apply Finset.ext;intro v
            have lt : v.val< t:=v.isLt.trans_le (Nat.le_of_not_gt time)
            simp only [U,Finset.mem_filter,lt,lt.trans_le (Nat.le_succ t),and_true]
          have ne : N (t+1)=N t:=congrArg (greedyNet x.dist R) ue
          simp [time] at step;rw [step,ne];exact sel p
  obtain ⟨_,old,sel⟩:=inv x.rows (by omega)
  let y:=X x.rows
  have full : U x.rows=W:=by ext p;simp [U,show p.val< x.rows by have:=p.isLt;omega]
  have net : N x.rows=greedyNet x.dist R W:=by unfold N;rw [full]
  have se (p : Point x.n) : selected y p.val ↔ p∈greedyNet x.dist R W:=by rw [←net];exact sel p
  have sc : unitR y=R:=by unfold unitR R;rw [old 0 (by omega),old 1 lo];rfl
  have wb (p : Point x.n) : inside y p.val ↔ p∈W:=by
        change 0< center _ (2+p.val) 0 ↔ p∈Finset.univ.filter (fun q : Point x.n=>inside x q.val)
        rw [Finset.mem_filter,old _ (pt p)];simp [inside]
  have post (r : ℕ) (hr : r< x.rows) (s : Bool) : field out r 0 s=expose y r 0 s:=endpass _ hr _ hk s
  have pair (a i : Point x.n) (s : Bool) :
      field out (pairRow x.n a.val i.val) 0 s=(if rect y a.val i.val s then 1 else 0):=by
    have size:=nextDigit i.isLt a.isLt 0
    let row:=pairRow x.n a.val i.val
    have hi : row< x.rows:=by dsimp [row,pairRow];omega
    have pr:=post row hi s
    have ix : subR y row (2+x.n)=a.val*x.n+i.val:=subAt y _ _ (by change a.val*x.n+i.val< x.rows;omega)
    have div:=divAt y a.val i.val (by change a.val< x.rows;have:=a.isLt;omega) i.isLt
    have rem:=remAt y a.val i.val (by change a.val< x.rows;have:=a.isLt;omega) i.isLt (by change i.val< x.rows;have:=i.isLt;omega)
    have ge : 2+x.n≤ row:=by dsimp [row,pairRow];omega
    have ix' : subR y row (2+y.n)=a.val*y.n+i.val:=ix
    simp [expose,show ¬row<2+y.n by change ¬row<2+x.n;omega,show 2+y.n≤ row from ge,ix',div,rem] at pr
    exact pr
  have flagOK (P : Prop) : (0<(if P then (1:ℤ) else 0)) ↔ P:=by by_cases h : P <;> simp [h]
  refine ⟨?_,?_,?_⟩
  · intro i
    have bound:2+i.val<2+y.n:=by change 2+i.val<2+x.n;have:=i.isLt;omega
    have f:=post (2+i.val) (pt i) false;have t:=post (2+i.val) (pt i) true
    have sub : subR y (2+i.val) 2=i.val:=subAt y _ _ (by change i.val< x.rows;have:=i.isLt;omega)
    simp [expose,bound,field,sub] at f t
    refine ⟨?_,?_⟩
    · change 0< witness out _ _ ↔ _;rw [t];exact se i
    · change center out _ _=_;rw [f];exact keyCorrect x.dist R W y i rfl (fun a=>finDist x a i) sc se
  · intro a i;change 0< field out _ _ false ↔ _
    rw [pair,flagOK];have d : FewBallRows.distAt y a.val i.val=x.dist a i:=finDist x a i
    simp [rect,wb,d,sc,window,ball,W,R]
  · intro a i;change 0< field out _ _ true ↔ _;rw [pair,flagOK]
    have d : FewBallRows.distAt y a.val.val i.val.val=x.dist a.val i.val:=finDist x _ _
    have e : FewBallRows.distAt y i.val.val a.val.val=x.dist i.val a.val:=finDist x _ _
    change _ ↔ a.val≠i.val ∧ a.val∈greedyNet x.dist R W ∧ i.val∈greedyNet x.dist R W ∧ x.dist a.val i.val≤8*R ∧ x.dist i.val a.val≤8*R
    simp [rect,se,d,e,sc,Fin.ext_iff,a.property,i.property]
    intro _ _;constructor
    · intro h eq;exact h (congrArg (fun s : ↥(greedyNet x.dist R W)=>s.val.val) eq)
    · intro h eq;exact h (Subtype.ext (Fin.ext eq))
