-- Prove2me | solution 1 for StableMSR.Recovery.WindowPorts.port_packing_preserves_derivations
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:21:54.736126+00:00
-- url     : https://prove2.me/submissions/f2f5d6de-19e8-4ecf-9f5c-e1ed53939005

import Definitions.Def_StableMSR_WindowPortPacking
import Theorems.Thm_StableMSR_Recovery_WindowPorts_factored_ports_exact_witnesses
import Theorems.Thm_StableMSR_Recovery_WindowPorts_counted_state_addresses
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
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
private structure Same (k : ℕ) (g h : Rules) : Prop where
  size : g.size=h.size
  widths : ∀v,g.len v=h.len v
  cap : ∀v,g.len v≤ k
  fields : ∀q,q< g.size → g.dst q=h.dst q ∧ (g.fork q ↔ h.fork q) ∧ g.lhs q=h.lhs q ∧ g.rhs q=h.rhs q ∧
      ∀j< k,∀s,g.payload q j s=h.payload q j s
private def Same.flip {k : ℕ} {g h : Rules} (s : Same k g h) : Same k h g where
  size:=s.size.symm
  widths:=fun v=>(s.widths v).symm
  cap:=fun v=>s.widths v ▸ s.cap v
  fields:=by
    intro q hq;obtain ⟨a,b,c,d,e⟩:=s.fields q (s.size.symm ▸ hq)
    exact ⟨a.symm,b.symm,c.symm,d.symm,fun j hj w=>(e j hj w).symm⟩
private lemma through {k : ℕ} {g h : Rules} (S : Same k g h) :
    ∀v w,Derives k g v w → Derives k h v w:=by
  intro v w der;induction der with
  | @leaf v q a no =>
    obtain ⟨dst,fork,_,_,pay⟩:=S.fields q a.1
    have eq : atomWord g v q=atomWord h v q:=by
      funext j s;by_cases lo : j< g.len v
      · simp only [atomWord,←S.widths,if_pos lo,pay j (lo.trans_le (S.cap v)) s]
      · simp only [atomWord,←S.widths,if_neg lo]
    rw [eq];exact .leaf ⟨S.size ▸ a.1,dst.symm.trans a.2⟩ (fun f=>no (fork.mpr f))
  | @join v q u w a f jt dl dr il ir =>
    obtain ⟨dst,fork,l,r,_⟩:=S.fields q a.1
    have valid : joint h v q:=by unfold joint at *;simpa only [←l,←r,←S.widths] using jt
    rw [S.widths (g.lhs q),l,S.widths v]
    exact .join ⟨S.size ▸ a.1,dst.symm.trans a.2⟩ (fork.mp f) valid (l ▸ il) (r ▸ ir)
private lemma division (y : World) (hn : 0< y.n) (a : ℕ) (h : a< y.rows) :
    divN y a=a/y.n ∧ remN y a=a%y.n:=by
  have hq:=(Nat.div_le_self a y.n).trans_lt h
  have hr:=(Nat.mod_le a y.n).trans_lt h
  have eq:=Nat.div_add_mod' a y.n
  exact ⟨by simpa only [eq] using divAt y (a/y.n) (a%y.n) hq (Nat.mod_lt _ hn),
    by simpa only [eq] using remAt y (a/y.n) (a%y.n) hq (Nat.mod_lt _ hn) hr⟩
private lemma digits (y : World) (hn : 0< y.n) (z : ℕ) (hz : z< y.rows) :
    reader y z=sourceRow y.n z ∧ leftDigit y z=firstCount y.n z ∧ rightDigit y z=lastCount y.n z:=by
  have lo : z-1< y.rows:=by omega
  have t:=division y hn (z-1) lo
  have s:=division y hn ((z-1)/y.n) ((Nat.div_le_self ..).trans_lt lo)
  simp only [reader,leftDigit,rightDigit,sourceRow,firstCount,lastCount,t.1,t.2,s.1,s.2,and_self]
private lemma written {y z : World} (f : Writes y z WindowPorts.packed) (hk : 0< y.k) (r : room y)
    (eq : slots z=WindowPorts.capacity y) (ke : z.k=y.k) (b q j : ℕ) (hb : 1≤ b ∧ b≤4) (hq : q< WindowPorts.capacity y)
    (hj : j< y.k) (s : Bool) : band z b q j s=contents y b q j s:=by
  let V:=WindowPorts.capacity y
  have spacious : 1+5*V< y.rows:=r
  have hq':q< V:=hq
  have low : q< y.rows:=by omega
  have qp:=subAt y (1+b*V) q low
  have slot : q< slots z:=eq.symm ▸ hq
  have bl : j< z.k:=ke.symm ▸ hj
  unfold band;rw [if_pos ⟨slot,bl⟩,eq]
  change field z (1+b*V+q) j s=contents y b q j s
  rw [f _ (by obtain ⟨_,_⟩:=hb;interval_cases b <;> omega) _ hj s]
  change (if 1+b*V+q=0 then _ else if 1+b*V+q=y.rows-1 then _ else if 1+b*V+q≤ V then _
    else if 1+b*V+q≤2*V then _ else if 1+b*V+q≤3*V then _ else if 1+b*V+q≤4*V then _ else _)=_
  obtain ⟨_,_⟩:=hb
  interval_cases b <;> (try simp only [Nat.one_mul] at qp ⊢) <;>
    (repeat' first | rw [if_neg (by omega)] | rw [if_pos (by omega)]) <;> rw [qp]
private lemma legalTwice (n : ℕ) (z : ℤ) : legalize n (legalize n z)=legalize n z:=by
  by_cases h : 0≤ z ∧ z<(n:ℤ)
  · simp [legalize,h]
  · rw [show legalize n z=0 from if_neg h];simp [legalize]
theorem solution (x : World) (e : ℚ) (H : ℕ) (m f : WindowProfiles.Mem) (hk : 1≤ x.k) (kn : x.k< x.n)
    (cert : Presents x e {x with rows:=H,mem:=m})
    (fill : Writes {x with rows:=H,mem:=m} {x with rows:=H,mem:=f} WindowPorts.packed) :
    Encodes x e {x with rows:=H,mem:=f} := by
  let y : World:={x with rows:=H,mem:=m}
  let z : World:={x with rows:=H,mem:=f}
  let B:=board y;let V:=WindowPorts.capacity y;let g:=lower B x.n x.k;let o:=decode z
  have space:1+5*V< H:=cert.space
  have vp : 0< V:=by dsimp [V,WindowPorts.capacity,volume];omega
  have hk':0< y.k:=hk
  have hn : 0< y.n:=by change 0< x.n;omega
  have sk : slots z=V:=by
    have eq:=fill 0 (by change 0< H;omega) 0 hk' false
    change center z 0 0=WindowPorts.packed y 0 0 false at eq
    unfold slots;rw [eq];simp [WindowPorts.packed,V]
  have tail : storedScenes z=y.mem 1:=by
    have eq:=fill (H-1) (by change H-1< H;omega) 0 hk' false
    change center z (H-1) 0=WindowPorts.packed y (H-1) 0 false at eq
    change center z (H-1) 0=_;rw [eq];simp [WindowPorts.packed,show H-1≠0 by omega,y]
  have wr (b q j : ℕ) (hb : 1≤ b ∧ b≤4) (hq : q< V) (hj : j< x.k) (s : Bool) :
      band z b q j s=contents y b q j s:=written fill hk' cert.space sk rfl b q j hb hq hj s
  have ds (q : ℕ) (hq : q< V):=digits y hn q (by change q< H;omega)
  have sizes : g.size=o.size:=sk.symm
  have width (v : ℕ) : g.len v=o.len v:=by
    by_cases h : v< V
    · have raw:=wr 2 v 0 (by decide) h hk' false
      change band z 2 v 0 false=(rightDigit y v:ℤ) at raw
      change (if v< V then min x.k (expandLen x.n v) else 0)=min x.k (band z 2 v 0 false).toNat
      rw [if_pos h,raw,(ds v h).2.2];rfl
    · change (if v< V then _ else 0)=min x.k (band z 2 v 0 false).toNat
      have hl : ¬v< slots z:=by rwa [sk]
      simp [h,band,hl]
  have share : Same x.k g o:=by
    refine ⟨sizes,width,?_,?_⟩
    · intro v;rw [width];exact Nat.min_le_left .. 
    · intro q hi
      change q< V at hi;obtain ⟨Q,A,D⟩:=ds q hi
      have W (b : ℕ) (hb : 1≤ b ∧ b≤4) (s : Bool):=wr b q 0 hb hi hk' s
      have dd:=W 3 (by decide) false;have ff:=W 3 (by decide) true
      have ll:=W 4 (by decide) false;have rr:=W 4 (by decide) true
      simp [contents,Q,A,D] at dd ff ll rr
      refine ⟨?_,?_,?_,?_,?_⟩
      · exact dd.symm
      · change (q≠0 ∧ B.tag (sourceRow x.n q)≠0) ↔ 0< band z 3 q 0 true
        rw [ff];change _ ↔ 0<(if q≠0 ∧ B.tag (sourceRow x.n q)≠0 then (1:ℤ) else 0)
        by_cases h : q≠0 ∧ B.tag (sourceRow x.n q)≠0 <;> simp [h]
      · change _=(band z 4 q 0 false).toNat;rw [ll];by_cases h : B.tag (sourceRow x.n q)=1 <;> simp [g,lower,B,y] at h ⊢ <;> simp [h]
      · change _=(band z 4 q 0 true).toNat;rw [rr];by_cases h : B.tag (sourceRow x.n q)=1 <;> simp [g,lower,B,y] at h ⊢ <;> simp [h]
      · intro j hj s;have ww:=wr 1 q j (by decide) hi hj s
        change _=legalize x.n (band z 1 q j s);rw [ww]
        by_cases eq : q=0
        · subst q;simp [g,lower,contents,legalize]
        · simp only [g,lower,eq,if_false,contents,if_true,Q]
          exact (legalTwice ..).symm
  refine ⟨?_,tail.trans cert.scenes,?_⟩
  · change 1+5*slots z< H;rwa [sk]
  · intro u hu i hi c hc
    let t:=u*x.n+i;let p:=B.root t;let r:=index x.n u i c
    obtain ⟨below,sp,all⟩:=cert.targets u hu i hi
    have ct : c< x.n:=by omega
    have lo:=nextDigit ct below 0
    have inc:=Nat.le_mul_of_pos_right (B.size*x.n) (show 0< x.n by omega)
    have ir : r< V:=by
      change t< B.size at below
      change t*x.n+c<1+B.size*x.n*x.n
      change t*x.n+c< B.size*x.n+0 at lo;omega
    have goal : o.goal r=finish x.n p c:=by
      have raw:=wr 2 r 0 (by decide) ir hk' true
      change band z 2 r 0 true=(finish y.n (B.root (divN y r)) (remN y r):ℤ) at raw
      have div:=division y hn r (by change r< H;omega)
      obtain ⟨a,b⟩:=splitRadix (a:=t) ct
      change r/y.n=t at a;change r%y.n=c at b
      change (band z 2 r 0 true).toNat=_;rw [raw,div.1,div.2,a,b];rfl
    obtain ⟨_,fin,_,len⟩:=(counted_state_addresses B x.n x.k hk kn).1 p sp c hc
    obtain ⟨sound,pad,covers⟩:=all c hc
    have iffD (w : Word) : Derives x.k o (finish x.n p c) w ↔ Reach x.k B p c w:=by
      let eq:=factored_ports_exact_witnesses B x.n x.k hk kn p c sp hc w
      exact ⟨fun h=>eq.mp (through share.flip _ _ h),fun h=>through share _ _ (eq.mpr h)⟩
    change r< o.size ∧ o.goal r< o.size ∧ o.len (o.goal r)=c ∧ _
    rw [goal]
    refine ⟨sizes ▸ ir,sizes ▸ fin,(width _).symm.trans len,fun w d=>sound w ((iffD _).mp d),?_,?_⟩
    · intro absent cz;obtain ⟨w,d⟩:=pad absent cz;exact ⟨w,(iffD _).mpr d⟩
    · intro present pos tw P ok cnt;obtain ⟨w,d,le⟩:=covers present pos tw P ok cnt;exact ⟨w,(iffD _).mpr d,le⟩
