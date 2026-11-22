-- Prove2me | solution 1 for StableMSR.Recovery.RegionalBallDP.regional_relaxation_optimal
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T13:13:53.643616+00:00
-- url     : https://prove2.me/submissions/810608d2-c98f-495a-9d64-5e0f86a70c15

import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
private abbrev V (x : World) (m : ℕ→ℤ) := withMem x m
private def Static (x : World) (m : ℕ→ℤ) := slots (V x m)=slots x ∧
  ∀r<x.rows,slots x<r → ∀j<x.k,∀w,field (V x m) r j w=field x r j w
private lemma width_le (x : World) (v : ℕ) : width x v≤x.k := by
  unfold width;split <;> simp
private lemma vb {x : World} (hs : shape x) {v : ℕ} (hv : vertex x v) : v<x.rows := by
  obtain ⟨_,h⟩:=hs;obtain ⟨_,a⟩:=hv;omega
private lemma baseStatic (x : World) (hk : 0<x.k) (hs : shape x) (m : ℕ→ℤ)
    (h : Writes x (V x m) seedTable) : Static x m := by
  have rh : 0<x.rows := by have e:=hs.2;omega
  constructor
  · unfold slots;congr 1;simpa [field,seedTable] using h 0 rh 0 hk false
  · intro r hr big j hj w;have nr : r≠0 := by omega
    simpa [seedTable,nr,not_le.mpr big] using h r hr j hj w
private lemma nextStatic (x : World) (hk : 0<x.k) (hs : shape x) (m m' : ℕ→ℤ)
    (s : Static x m) (h : Writes (V x m) (V x m') tick) : Static x m' := by
  have rh : 0<x.rows := by have e:=hs.2;omega
  constructor
  · apply Eq.trans _ s.1
    unfold slots;congr 1;simpa [field,tick] using h 0 rh 0 hk false
  · intro r hr big j hj w;have nr : r≠0 := by omega
    apply Eq.trans _ (s.2 r hr big j hj w)
    simpa [tick,nr,s.1,not_le.mpr big] using h r hr j hj w
private lemma sameWidth {x : World} {m : ℕ→ℤ} (s : Static x m) (hs : shape x) (hk : 0<x.k)
    {v : ℕ} (hv : vertex x v) : width (V x m) v=width x v := by
  obtain ⟨pos,lim⟩:=hs
  obtain ⟨vp,vl⟩:=hv
  have f:=s.2 (slots x+slots x+v) (by omega) (by omega) 0 hk false
  simp only [field,Bool.false_eq_true,if_false] at f
  simp only [width,s.1,f];rfl
private lemma sameParent {x : World} {m : ℕ→ℤ} (s : Static x m) (hs : shape x) (hk : 0<x.k)
    {q : ℕ} (hq : vertex x q) : parent (V x m) q=parent x q ∧ destination (V x m) q=destination x q := by
  obtain ⟨pos,lim⟩:=hs
  obtain ⟨qp,ql⟩:=hq
  have f:=s.2 (slots x+slots x+slots x+q) (by omega) (by omega) 0 hk
  constructor
  · unfold parent;rw [s.1];exact congrArg Int.toNat (f false)
  · unfold destination;rw [s.1];exact f true
private lemma sameLink {x : World} {m : ℕ→ℤ} (s : Static x m) (hs : shape x) (hk : 0<x.k)
    {v q : ℕ} (hv : vertex x v) : link (V x m) v q ↔ link x v q := by
  have ve (t : ℕ) : vertex (V x m) t ↔ vertex x t := by simp [vertex,s.1]
  by_cases hq : vertex x q
  · obtain ⟨p,d⟩:=sameParent s hs hk hq
    unfold link;rw [p,d,ve,ve,sameWidth s hs hk hv]
    by_cases hp : vertex x (parent x q)
    · rw [sameWidth s hs hk hp]
    · simp [hp]
  · simp [link,ve,hq]
private lemma sameSplice {x : World} {m : ℕ→ℤ} (s : Static x m) (hs : shape x) (hk : 0<x.k)
    {v q : ℕ} (hv : vertex x v) (l : link x v q) (u : Word) :
    splice (V x m) v q u=splice x v q u := by
  have p:=(sameParent s hs hk l.1).1
  have ww:=sameWidth s hs hk hv
  have wp:=sameWidth s hs hk l.2.1
  funext j b
  unfold splice;rw [p,ww,wp]
  by_cases a : j<width x (parent x q)
  · simp [a]
  by_cases t : j<width x v
  · have hj:=lt_of_lt_of_le t (width_le x v)
    have f:=s.2 (slots x+q) (by have e:=hs.2;have z:=l.1.2;omega) (by have z:=l.1.1;omega) j hj b
    simp only [a,t,if_false,if_true,payload,s.1,f];rfl
  · simp [a,t]
private lemma winner_exists (x : World) (v : ℕ) (h : ∃q<x.rows,eligible x v q) :
    ∃q<x.rows,winner x v q ∧ ∀z<x.rows,winner x v z → z=q := by
  classical
  let S:=(Finset.range x.rows).filter (eligible x v)
  have hs : S.Nonempty := by obtain ⟨j,hj,a⟩:=h;exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,a⟩⟩
  obtain ⟨u,hu,hmin⟩:=Finset.exists_min_image S (price x v) hs
  let T:=S.filter (fun q=>price x v q=price x v u)
  have ht : T.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩
  let q:=T.min' ht
  obtain ⟨qS,qE⟩:=Finset.mem_filter.mp (T.min'_mem ht)
  obtain ⟨qh,qe⟩:=Finset.mem_filter.mp qS
  have qr:=Finset.mem_range.mp qh
  have win : winner x v q := by
    refine ⟨qe,?_⟩;intro z hz ez
    have zs : z∈S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hz,ez⟩
    have zl:=hmin z zs
    change price x v q=price x v u at qE
    rcases lt_or_eq_of_le (qE.le.trans zl) with lt|eq
    · exact Or.inl lt
    · exact Or.inr ⟨eq,T.min'_le _ (Finset.mem_filter.mpr ⟨zs,eq.symm.trans qE⟩)⟩
  refine ⟨q,qr,win,?_⟩;intro z hz wz
  rcases win.2 z hz wz.1 with lt|⟨eq,le⟩ <;> rcases wz.2 q qr win.1 with rev|⟨eq',ge⟩
  · linarith
  · linarith
  · linarith
  · omega
private lemma slot_choice {x : World} {v q : ℕ} (hv : vertex x v) (nr : v≠1) (hq : q<x.rows)
    (wq : winner x v q) (un : ∀z<x.rows,winner x v z→z=q) (j : ℕ) (b : Bool) :
    tick x v j b=candidate x v q j b := by
  classical
  have v0 : v≠0 := Nat.ne_of_gt hv.1
  have ex : ∃q<x.rows,eligible x v q := ⟨q,hq,wq.1⟩
  simp only [tick,v0,if_false,hv.2,if_true,nr,ex]
  rw [Finset.sum_eq_single q]
  · simp [wq]
  · intro z hz hne
    exact if_neg (fun h=>hne (un z (Finset.mem_range.mp hz) h))
  · exact fun h=>False.elim (h (Finset.mem_range.mpr hq))
private lemma mono_splice (x : World) {v q : ℕ} (l : link x v q) {a b : Word}
    (h : weight x (width x (parent x q)) a≤weight x (width x (parent x q)) b) :
    weight x (width x v) (splice x v q a)≤weight x (width x v) (splice x v q b) := by
  let extra := ∑j ∈ Finset.range x.k,if width x (parent x q)≤j ∧ j<width x v then
    MinSumFPT.oracleAnswer x.dist (payload x q j false) (payload x q j true) else 0
  have add (u : Word) : weight x (width x v) (splice x v q u)=weight x (width x (parent x q)) u+extra := by
    unfold weight extra;rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro j _
    by_cases a : j<width x (parent x q)
    · have t:=lt_of_lt_of_le a l.2.2.2.2
      simp [splice,a,t,not_le.mpr a]
    · by_cases b : j<width x v <;> simp [splice,a,le_of_not_gt a,b]
  rw [add,add];linarith
private lemma isRoute {x : World} {i v : ℕ} {u : Word} (p : wave x i v u) : Route x v u := by
  induction i generalizing v u with
  | zero => obtain ⟨rfl,rfl⟩:=p;exact .root
  | succ i ih =>
    rcases p with ⟨rfl,rfl⟩|⟨q,a,hv,l,pr,rfl⟩
    · exact .root
    · exact .append hv l (ih pr)
private lemma byRound {x : World} {v : ℕ} {u : Word} (h : Route x v u) :
    ∀i,v ≤ i → wave x i v u := by
  induction h with
  | root => intro i _;cases i <;> simp [wave]
  | append hv l p ih =>
    intro i hi;cases i with
    | zero => have hp:=hv.1;omega
    | succ t => exact Or.inr ⟨_,_,hv,l,ih t (by have a:=l.2.2.1;omega),rfl⟩
private lemma legal_word {x : World} (hn : 0<x.n) {v : ℕ} {u : Word} (h : Route x v u) (j : ℕ) (b : Bool) :
    0≤u j b ∧ u j b<(x.n:ℤ) := by
  induction h with
  | root => simp [blank];omega
  | append hv l p ih =>
    unfold splice;split
    · exact ih
    · split
      · unfold payload legalize;split
        · assumption
        · omega
      · omega
private def Correct (x : World) (i : ℕ) (m : ℕ→ℤ) := ∀v,vertex x v →
    (live (V x m) v → wave x i v (word (V x m) v)) ∧
    (∀u,wave x i v u → live (V x m) v ∧
      weight x (width x v) (word (V x m) v) ≤ weight x (width x v) u)
private lemma baseOK (x : World) (hk : 0<x.k) (hs : shape x) (m : ℕ→ℤ)
    (h : Writes x (V x m) seedTable) : Correct x 0 m := by
  intro v hv
  have hv0:=Nat.ne_of_gt hv.1
  have fld (j : ℕ) (hj : j<x.k) (b : Bool) : field (V x m) v j b=if v=1 then 0 else -1 := by
    simpa [seedTable,hv0,hv.2] using h v (vb hs hv) j hj b
  by_cases root : v=1
  · subst v
    have row : word (V x m) 1=blank := by
      funext j b;by_cases hj : j<x.k
      · exact (if_pos hj).trans (by simpa [blank] using fld j hj b)
      · exact if_neg hj
    have act : live (V x m) 1 := by have c:=fld 0 hk false;change _≤field (V x m) 1 0 false;simp [c]
    refine ⟨fun _=>⟨rfl,row⟩,?_⟩
    intro u z;obtain ⟨_,rfl⟩:=z;exact ⟨act,by rw [row]⟩
  · have off : ¬ live (V x m) v := by
      have c:=fld 0 hk false;change ¬0≤field (V x m) v 0 false;simp [c,root]
    exact ⟨fun h=>(off h).elim,fun u z=>(root z.1).elim⟩
private lemma nextOK (x : World) (hk : 0<x.k) (hn : 0<x.n) (hs : shape x)
    (i : ℕ) (m m' : ℕ→ℤ) (s : Static x m) (ih : Correct x i m)
    (h : Writes (V x m) (V x m') tick) : Correct x (i+1) m' := by
  let y:=V x m
  let y':=V x m'
  intro v hv
  have hv' : vertex y v := ⟨hv.1,by change v≤ slots (V x m);rw [s.1];exact hv.2⟩
  have hv0:=Nat.ne_of_gt hv.1
  have vr:=vb hs hv
  have fld (j : ℕ) (hj : j<x.k) (b : Bool) : field y' v j b=tick y v j b := h v vr j hj b
  by_cases one : v=1
  · subst v
    have f (j : ℕ) (hj : j<x.k) (b : Bool) : field y' 1 j b=0 := by simpa [tick,hv'.2] using fld j hj b
    have row : word y' 1=blank := by
      funext j b;by_cases hj : j<x.k
      · exact (if_pos hj).trans (f j hj b)
      · exact if_neg hj
    have act : live y' 1 := by change 0≤field y' 1 0 false;rw [f 0 hk false]
    refine ⟨fun _=>Or.inl ⟨rfl,row⟩,?_⟩
    intro u hu
    rcases hu with ⟨_,rfl⟩|⟨q,a,_,l,_,_⟩
    · exact ⟨act,by change weight x _ (word y' 1)≤_;rw [row]⟩
    · have pos:=l.2.1.1;have lt:=l.2.2.1;omega
  have convertEligible {q : ℕ} (eligible' : eligible y v q) :
      link x v q ∧ live y (parent x q) := by
    have l:=(sameLink s hs hk hv).mp eligible'.1
    have eq:=(sameParent s hs hk l.1).1
    exact ⟨l,by simpa only [y,eq] using eligible'.2⟩
  have getEdge {u : Word} (hu : wave x (i+1) v u) :
      ∃q<x.rows,eligible y v q ∧ ∃a,wave x i (parent x q) a ∧ u=splice x v q a := by
    rcases hu with ⟨eq,_⟩|⟨q,a,_,l,prev,rfl⟩
    · contradiction
    have eq:=(sameParent s hs hk l.1).1
    have ac:=(ih _ l.2.1).2 _ prev
    exact ⟨q,vb hs l.1,⟨(sameLink s hs hk hv).mpr l,by simpa only [y,eq] using ac.1⟩,a,prev,rfl⟩
  have cand {q : ℕ} (l : link x v q) : candidate y v q=splice x v q (word y (parent x q)) := by
    unfold candidate;rw [show parent y q=parent x q from (sameParent s hs hk l.1).1]
    exact sameSplice s hs hk hv l _
  have pr {q : ℕ} (l : link x v q) : price y v q=weight x (width x v) (splice x v q (word y (parent x q))) := by
    unfold price;rw [show width y v=width x v from sameWidth s hs hk hv,cand l];rfl
  by_cases ex : ∃q<x.rows,eligible y v q
  · obtain ⟨q,hq,wq,unique⟩:=winner_exists y v ex
    obtain ⟨l,act⟩:=convertEligible wq.1
    have prev:=(ih _ l.2.1).1 act
    have path : wave x (i+1) v (candidate y v q) :=
      Or.inr ⟨q,word y (parent x q),hv,l,prev,cand l⟩
    have row : word y' v=candidate y v q := by
      funext j b;by_cases hj : j<x.k
      · exact (if_pos hj).trans ((fld j hj b).trans (slot_choice hv' one hq wq unique j b))
      · have aa : ¬j<width x (parent x q) := by have z:=width_le x (parent x q);omega
        have bb : ¬j<width x v := by have z:=width_le x v;omega
        rw [cand l];simp [word,splice,aa,bb,y',V,withMem,hj]
    have act' : live y' v := by
      have valid:=(legal_word hn (isRoute path) 0 false).1
      rw [←row] at valid
      change 0≤field y' v 0 false
      exact (show word y' v 0 false=field y' v 0 false from if_pos hk) ▸ valid
    refine ⟨fun _=>row.symm ▸ path,?_⟩
    intro u hu
    obtain ⟨z,hz,el,a,pa,rfl⟩:=getEdge hu
    have lz:=(convertEligible el).1
    have minimum : price y v q≤price y v z := by
      rcases wq.2 z hz el with lt|⟨eq,_⟩
      · exact lt.le
      · exact eq.le
    refine ⟨act',?_⟩
    change weight x (width x v) (word y' v)≤_
    rw [row,cand l,←pr l] 
    exact minimum.trans (by rw [pr lz];exact mono_splice x lz ((ih _ lz.2.1).2 _ pa).2)
  · have ex' : ¬∃q<y.rows,eligible y v q := ex
    have f : field y' v 0 false = -1 := by simpa only [tick,hv0,if_false,hv'.2,if_true,one,ex'] using fld 0 hk false
    have off : ¬live y' v := by change ¬0≤field y' v 0 false;rw [f];decide
    refine ⟨fun a=>(off a).elim,?_⟩
    intro u hu
    obtain ⟨q,hq,el,_⟩:=getEdge hu
    exact (ex ⟨q,hq,el⟩).elim
theorem solution (x : World) (hk : 0<x.k) (hn : 0<x.n) (hs : shape x)
    (h : ℕ→ℕ→ℤ) (a : Writes x (withMem x (h 0)) seedTable)
    (b : ∀i<x.rows,Writes (withMem x (h i)) (withMem x (h (i+1))) tick)
    (m : ℕ→ℤ) (c : Writes (withMem x (h x.rows)) (withMem x m) clean) :
    endpoints (withMem x m) ∧ ∀v,vertex x v → ∀u,Route x v u →
      Route x v (word (withMem x m) v) ∧
      weight x (width x v) (word (withMem x m) v) ≤ weight x (width x v) u := by
  have all (i : ℕ) (hi : i≤x.rows) : Static x (h i) ∧ Correct x i (h i) := by
    induction i with
    | zero => exact ⟨baseStatic x hk hs _ a,baseOK x hk hs _ a⟩
    | succ i ih =>
      obtain ⟨s,ok⟩:=ih (by omega)
      exact ⟨nextStatic x hk hs _ _ s (b i (by omega)),nextOK x hk hn hs i _ _ s ok (b i (by omega))⟩
  obtain ⟨_,ok⟩:=all x.rows (by omega)
  let y:=V x (h x.rows)
  let z:=V x m
  have cl (r : ℕ) (hr : r<x.rows) (j : ℕ) (hj : j<x.k) (b : Bool) :
      field z r j b=legalize x.n (field y r j b) := c r hr j hj b
  have sane (v : ℤ) : ∃a : Fin x.n,legalize x.n v=(a.val:ℤ) := by
    unfold legalize;split
    · rename_i hh;exact ⟨⟨v.toNat,by omega⟩,by simp [Int.toNat_of_nonneg hh.1]⟩
    · exact ⟨⟨0,hn⟩,rfl⟩
  refine ⟨?_,?_⟩
  · intro r hr j hj
    obtain ⟨a,ha⟩:=sane (field y r j false)
    obtain ⟨b,hb⟩:=sane (field y r j true)
    exact ⟨a,b,(cl r hr j hj false).trans ha,(cl r hr j hj true).trans hb⟩
  · intro v hv u path
    have full:=byRound path x.rows (vb hs hv).le
    obtain ⟨active,le⟩:=(ok v hv).2 _ full
    have got : Route x v (word y v) := isRoute ((ok v hv).1 active)
    have row : word z v=word y v := by
      funext j b
      by_cases hj : j<x.k
      · have bb:=legal_word hn got j b
        have e : word y v j b=field y v j b := if_pos hj
        rw [e] at bb
        exact (show word z v j b=field z v j b from if_pos hj).trans
          ((cl v (vb hs hv) j hj b).trans ((if_pos bb).trans e.symm))
      · exact (if_neg hj).trans (if_neg hj).symm
    change Route x v (word z v) ∧ weight x _ (word z v)≤_
    rw [row];exact ⟨got,le⟩

