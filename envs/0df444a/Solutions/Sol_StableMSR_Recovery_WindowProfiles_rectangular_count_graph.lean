-- Prove2me | solution 1 for StableMSR.Recovery.WindowProfiles.rectangular_count_graph
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:17:39.597118+00:00
-- url     : https://prove2.me/submissions/f4db9bce-cbd0-4aaf-92f9-a05e314453c5

import Definitions.Def_StableMSR_WindowProfilePacking
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

open StableMSR.Recovery.RegionalBallDP (field parent destination width payload link slots vertex shape)
private lemma nextSlot {n a b i : ℕ} (hi : i< n) (h : a< b) (j : ℕ) : a*n+i< b*n+j:=by
  have h₁ : a*n+i<(a+1)*n:=by rw [Nat.succ_mul];omega
  exact h₁.trans_le ((Nat.mul_le_mul_right n h).trans (Nat.le_add_right ..))
private lemma injectSlot {n p q a b : ℕ} (a0 : a< n) (b0 : b< n) (eq : p*n+a=q*n+b) :
    p=q ∧ a=b:=by
  have h : p=q:=by
    rcases lt_trichotomy p q with lo|same|hi
    · exact (ne_of_lt (nextSlot a0 lo b) eq).elim
    · exact same
    · exact (ne_of_lt (nextSlot b0 hi a) eq.symm).elim
  subst q;exact ⟨rfl,Nat.add_left_cancel eq⟩
private lemma eqNode {n u v i j b c : ℕ} (hi : i< n) (hj : j< n) (hb : b< n) (hc : c< n)
    (H : node n u i b=node n v j c) : u=v ∧ i=j ∧ b=c:=by
  have h:=injectSlot hb hc (Nat.add_left_cancel H)
  have h':=injectSlot hi hj h.1;exact ⟨h'.1,h'.2,h.2⟩
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
    · have q:=nextSlot hd more 0;omega
  · intro h;exact (h (Finset.mem_range.mpr hp)).elim
private lemma remAt (x : World) (p d : ℕ) (hp : p< x.rows) (hd : d< x.n) (dr : d< x.rows) :
    remN x (p*x.n+d)=d:=by rw [remN,divAt x p d hp hd,subAt _ _ _ dr]
private lemma decode {n S q : ℕ} (hn : 0< n) (lo : 2≤ q) (hi : q≤ capacity S n) :
    ∃u< S,∃i< n,∃a< n,∃b< n,q=arc n u i a b:=by
  let z:=q-2;let v:=z/n;let t:=v/n
  have zlt : z< S*n*n*n:=by dsimp [z,capacity] at *;omega
  have vl : v< S*n*n:=(Nat.div_lt_iff_lt_mul hn).mpr zlt
  have tl : t< S*n:=(Nat.div_lt_iff_lt_mul hn).mpr vl
  have ul : t/n< S:=(Nat.div_lt_iff_lt_mul hn).mpr tl
  have eq (a : ℕ) : a/n*n+a%n=a:=by simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div a n
  refine ⟨t/n,ul,t%n,Nat.mod_lt _ hn,v%n,Nat.mod_lt _ hn,z%n,Nat.mod_lt _ hn,?_⟩
  unfold arc index;rw [Nat.add_assoc,eq t,show t*n+v%n=v from eq v,show v*n+z%n=z from eq z];dsimp [z];omega
theorem solution (x : World) (hk : 1≤ x.k) (hn : x.k< x.n) (m : Mem)
    (tab : ∀r< height x,∀j< x.k,∀w,RegionalBallDP.field (arena x m) r j w=
      packed ({x with rows:=height x,mem:=Function.update x.mem 0 (x.rows:ℤ)}) r j w) : Grid x m := by
  classical
  let n:=x.n;let k:=x.k;let S:=x.rows;let M:=capacity S n
  let H:=height x;let y : World:={x with rows:=H,mem:=Function.update x.mem 0 (S:ℤ)}
  let g:=arena x m
  have heightEq : H=4*M+1:=rfl
  have mpos : 0< M:=by dsimp [M,capacity];omega
  have Mval : dim y=M:=by unfold dim;change capacity ((Function.update x.mem 0 (S:ℤ)) 0).toNat n=M;simp [M]
  have old (r j : ℕ) (b : Bool) : field y r j b=field x r j b:=by
    cases b <;> simp [field,center,witness,y,addr,Function.update_of_ne,show ∀v : ℕ,3+v≠0 by omega]
  have live (u i c : ℕ) : active y u i c ↔ active x u i c:=by
    change (0≤ field y (index n u i c) 0 false) ↔ 0≤ field x (index n u i c) 0 false;rw [old]
  have wr (r j : ℕ) (hr : r< H) (hj : j< k) (b : Bool) : field g r j b=packed y r j b:=tab r hr j hj b
  have sm : slots g=M:=by
    have z:=wr 0 0 (by omega) hk false
    change center g 0 0=packed y 0 0 false at z;unfold slots;rw [z];simp [packed,Mval]
  have bounds (u i a b : ℕ) (hu : u< S) (hi : i< n) (ha : a< n) (hb : b< n) :
      u< H ∧ n≤ H ∧ u*n+i< H ∧ index n u i a< H ∧ arc n u i a b≤ M ∧ node n u i b≤ M:=by
    have p1:=nextSlot hi hu 0;have p2:=nextSlot ha (show u*n+i< S*n by omega) 0
    have p2b:=nextSlot hb (show u*n+i< S*n by omega) 0
    have p3:=nextSlot hb (show (u*n+i)*n+a< S*n*n by omega) 0
    have npos : 1≤ n:=by dsimp [n];omega
    have ge1 : S≤ S*n:=Nat.le_mul_of_pos_right _ npos
    have ge2 : S*n≤ S*n*n:=Nat.le_mul_of_pos_right _ npos
    have ge3 : S*n*n≤ S*n*n*n:=Nat.le_mul_of_pos_right _ npos
    have geN : n≤ S*n:=Nat.le_mul_of_pos_left _ (by omega)
    dsimp only [M,capacity,node,index,arc] at *;omega
  have state (u : ℕ) (hu : u< S) (i : ℕ) (hi : i< n) (b : ℕ) (hb : b≤ k) :
      vertex g (node n u i b) ∧ width g (node n u i b)=b:=by
    have bl : b< n:=by change b≤ x.k at hb;change b< x.n;omega
    obtain ⟨_,nH,iH,_,_,vM⟩:=bounds u i b b hu hi bl bl
    let v:=node n u i b
    have low : 2≤ v:=by dsimp [v,node];omega
    have cap : v≤ M:=vM
    have eq:=wr (M+M+v) 0 (by omega) hk false
    have raw : subR y (M+M+v) (M+M+2)=index n u i b:=by
      rw [show M+M+v=M+M+2+index n u i b by dsimp [v,node];omega];exact subAt _ _ _ (by change index n u i b< H;dsimp [v,node] at cap;omega)
    have rem : remN y (index n u i b)=b:=remAt y _ _ iH bl (by change b< H;omega)
    have val : center g (M+M+v) 0=(b:ℤ):=by
      change field g _ _ false=_;rw [eq]
      simp only [packed,Mval,if_neg (by omega : M+M+v≠0),if_neg (by omega : ¬M+M+v≤ M),
        if_neg (by omega : ¬M+M+v≤ M+M),if_pos (by omega : M+M+v≤ M+M+M),raw,rem]
    refine ⟨⟨by omega,sm ▸ cap⟩,?_⟩
    change (if v=1 then 0 else min k (center g (slots g+slots g+v) 0).toNat)=b
    rw [if_neg (by omega),sm,val,Int.toNat_natCast,Nat.min_eq_right hb]
  have one : destination g 1=0:=by
    unfold destination;rw [sm];change field g (M+M+M+1) 0 true=_
    rw [wr (M+M+M+1) 0 (by omega) hk true]
    simp only [packed,Mval,if_neg (by omega : M+M+M+1≠0),if_neg (by omega : ¬M+M+M+1≤ M),
      if_neg (by omega : ¬M+M+M+1≤ M+M),if_neg (by omega : ¬M+M+M+1≤ M+M+M),
      if_neg (by omega : ¬M+M+M+2≤ M+M+M+1)]
  have edgeInfo (u i a b : ℕ) (hu : u< S) (hi : i< n) (ha : a< n) (hb : b< n) :
      let q:=arc n u i a b
      (destination g q=if allowed x u i a b ∧ b≤ k then (node n u i b:ℤ) else 0) ∧
      (allowed x u i a b → b≤ k → parent g q=prior n u i a) ∧
      ∀j< k,∀side,payload g q j side=token x u i (b-a) (j-a) side:=by
    let q:=arc n u i a b;let z:=index n u i a*n+b
    have hq : q=2+z:=by dsimp [q,z,arc];omega
    obtain ⟨uH,nH,iH,aH,qM,_⟩:=bounds u i a b hu hi ha hb
    have v1:=divAt y (index n u i a) b aH hb
    have v2:=divAt y (u*n+i) a iH ha
    have v3:=divAt y u i uH hi
    have r1:=remAt y (index n u i a) b aH hb (by change b< H;omega)
    have r2:=remAt y (u*n+i) a iH ha (by change a< H;omega)
    have r3:=remAt y u i uH hi (by change i< H;omega)
    change divN y z=index n u i a at v1;change remN y z=b at r1
    change divN y (index n u i a)=u*n+i at v2;change remN y (index n u i a)=a at r2
    change divN y (u*n+i)=u at v3;change remN y (u*n+i)=i at r3
    have zH : z< H:=by change q≤ M at qM;omega
    have off (L) : subR y (L+q) (L+2)=z:=by rw [show L+q=L+2+z by omega];exact subAt _ _ _ zH
    have orig : (y.mem 0).toNat=S:=by simp [y]
    have diff:=subSmall y b a (by change b< H;omega)
    have cond : (u<(y.mem 0).toNat ∧ a≤ b ∧ b≤ k ∧ (i=0 → a=0) ∧ active y u i (subR y b a)) ↔
        allowed x u i a b ∧ b≤ k:=by rw [orig,diff,live];unfold allowed;tauto
    have edgeInfo' (side : Bool) : field g (M+M+M+q) 0 side=
        if allowed x u i a b ∧ b≤ k then (if side then (node n u i b:ℤ) else (prior n u i a:ℤ)) else 0:=by
      have qle : q≤ M:=qM
      rw [wr (M+M+M+q) 0 (by omega) hk side]
      simp only [packed,Mval,if_neg (by omega : M+M+M+q≠0),if_neg (by omega : ¬M+M+M+q≤ M),
        if_neg (by omega : ¬M+M+M+q≤ M+M),if_neg (by omega : ¬M+M+M+q≤ M+M+M),
        if_pos (by omega : M+M+M+2≤ M+M+M+q),off,edgeField,v1,v2,v3,r1,r2,r3]
      change (if u<(y.mem 0).toNat ∧ a≤ b ∧ b≤ k ∧ (i=0 → a=0) ∧ active y u i (subR y b a) then _ else 0)=_
      by_cases h : allowed x u i a b ∧ b≤ k
      · simp only [if_pos (cond.mpr h),if_pos h,prior,show y.n=n from rfl]
      · rw [if_neg (mt cond.mp h),if_neg h]
    refine ⟨?_,?_,?_⟩
    · unfold destination;rw [sm];exact edgeInfo' true
    · intro act bound;unfold parent;rw [sm]
      have ep:=edgeInfo' false;rw [if_pos ⟨act,bound⟩] at ep
      change (field g _ 0 false).toNat=_;rw [ep];simp
    · intro j hj side;unfold payload;rw [sm]
      have qle : q≤ M:=qM
      rw [wr (M+q) j (by omega) hj side]
      have jH : j< H:=by change j< x.k at hj;change x.n≤ H at nH;omega
      simp only [packed,Mval,if_neg (by omega : M+q≠0),if_neg (by omega : ¬M+q≤ M),
        if_pos (by omega : M+q≤ M+M),off,dataWord,v1,v2,v3,r1,r2,r3,diff,subSmall y j a jH]
      change RegionalBallDP.legalize x.n (field y (index n u i (b-a)) (j-a) side)=_
      rw [old];rfl
  refine ⟨⟨sm ▸ mpos,by change 4*slots g< H;rw [sm];omega⟩,state,?_,?_⟩
  · intro u hu i hi b hb q lk
    have ne : node n u i b≠0:=by unfold node;omega
    have qlo:=lk.1.1;have qhi:=lk.1.2;change q≤ slots g at qhi;rw [sm] at qhi
    have des:=lk.2.2.2.1
    by_cases oneQ : q=1
    · subst q;rw [one] at des;exact (ne (by exact_mod_cast des.symm)).elim
    obtain ⟨v,hv,j,hj,c,hc,d,hd,eq⟩:=decode (by dsimp [n];omega) (by omega) qhi
    subst q
    rw [(edgeInfo v j c d hv hj hc hd).1] at des
    split at des
    next yes =>
      have E : node n v j d=node n u i b:=by exact_mod_cast des
      have eqs:=eqNode hj hi hd (by change b< x.n;omega) E
      obtain ⟨rfl,rfl,rfl⟩:=eqs;exact ⟨c,yes.1,rfl⟩
    next _ => exact (ne (by exact_mod_cast des.symm)).elim
  · intro u hu i hi b hb a ok
    have ab:=ok.1
    have bl : b< n:=by change b< x.n;omega
    have al : a< n:=by omega
    obtain ⟨des,par,vals⟩:=edgeInfo u i a b hu hi al bl
    rw [if_pos ⟨ok,hb⟩] at des
    have par':=par ok hb
    have pv : vertex g (prior n u i a) ∧ width g (prior n u i a)=a ∧ prior n u i a< node n u i b:=by
      cases i with
      | zero =>
        refine ⟨⟨by change 0<(1:ℕ);decide,sm ▸ mpos⟩,(if_pos rfl : width g 1=0) |>.trans (ok.2.1 rfl).symm,?_⟩
        dsimp [prior,node];omega
      | succ i =>
        obtain ⟨v,h⟩:=state u hu i (by change i< x.n;omega) a (by change a≤ x.k;omega)
        refine ⟨v,h,?_⟩;change 2+((u*n+i)*n+a)<2+((u*n+(i+1))*n+b)
        have lt:=nextSlot al (show u*n+i< u*n+(i+1) by omega) b;omega
    have lim:=(bounds u i a b hu hi al bl).2.2.2.2.1
    refine ⟨⟨⟨by unfold arc;omega,sm ▸ lim⟩,par' ▸ pv.1,par' ▸ pv.2.2,des,?_⟩,par',?_⟩
    · rw [par',pv.2.1,(state u hu i hi b hb).2];exact ab
    · intro j _ jl w;exact vals j (by omega) w

