-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.topological_join_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:52:54.908063+00:00
-- url     : https://prove2.me/submissions/bd10a4f1-3774-4970-975b-f6bb4ea8f37f

import Theorems.Thm_StableMSR_Recovery_WindowJoins_minimum_join_row
import Definitions.Def_StableMSR_WindowJoins
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
private abbrev V (x : World) (m : Mem) := replace x m
private def Frozen (x : World) (m : Mem) := slots (V x m)=slots x ∧ ∀r< x.rows,slots x< r →
  ∀j< x.k,∀w,field (V x m) r j w=field x r j w
private lemma parsed {x : World} (sh : shaped x) {m : Mem} (s : Frozen x m) : decode (V x m)=decode x :=by
  have bb (b : ℕ) (lo : 1≤ b) (hi : b≤4) : band (V x m) b=band x b:=by
    funext q j w;unfold band;rw [s.1,show (V x m).k=x.k from rfl]
    by_cases h : q< slots x ∧ j< x.k
    · simp only [if_pos h];have low:=Nat.mul_le_mul_right (slots x) lo;have up:=Nat.mul_le_mul_right (slots x) hi
      unfold shaped at sh;exact s.2 _ (by omega) (by omega) j h.2 w
    · exact (if_neg h).trans (if_neg h).symm
  simp only [decode,s.1,bb 1 (by decide) (by decide),bb 2 (by decide) (by decide),bb 3 (by decide) (by decide),bb 4 (by decide) (by decide)];rfl
private lemma copyWord {x y : World} (hk : y.k=x.k) (r s : ℕ)
    (f : ∀j< x.k,∀w,field y r j w=field x s j w) : word y r=word x s:=by
  funext j w;unfold word;rw [hk];by_cases h : j< x.k
  · exact (if_pos h).trans ((f j h w).trans (if_pos h).symm)
  · exact (if_neg h).trans (if_neg h).symm
private lemma sane (x : World) (hn : 0< x.n) : Sane x (decode x):=by
  refine ⟨fun v=>min_le_left ..,?_⟩;intro q j w;change 0≤ legalize x.n _ ∧ legalize x.n _<(x.n:ℤ)
  unfold legalize;split
  · assumption
  · omega
theorem solution (x : World) (hk : 0< x.k) (hn : 0< x.n) (sh : shaped x) (a : ℕ→Mem) (m : Mem)
    (init : Writes x (replace x (a 0)) seed)
    (steps : ∀i< x.rows,Writes (replace x (a i)) (replace x (a (i+1))) advance)
    (ending : Writes (replace x (a x.rows)) (replace x m) project) :
    let y:=replace x m;let g:=decode x
    storedScenes y=storedScenes x ∧ ∀r< g.size,g.goal r< g.size →
       RowOK x g (g.goal r) (0≤ center y r 0) (word y r) := by
  let g:=decode x
  have hp : 0< x.rows:=by unfold shaped at sh;omega
  have size : slots x< x.rows:=by unfold shaped at sh;omega
  have inv (t : ℕ) (ht : t≤ x.rows) : Frozen x (a t) ∧ witness (V x (a t)) 0 0=(t:ℤ) ∧
      ∀v< slots x,v< t → RowOK x g v (liveRow (V x (a t)) v) (rowWord (V x (a t)) v):=by
    induction t with
    | zero =>
      refine ⟨⟨?_,?_⟩,?_,fun v _ hv=>(Nat.not_lt_zero v hv).elim⟩
      · unfold slots;congr 1;simpa [field,seed] using init 0 hp 0 hk false
      · intro r hr big j hj w;have nz : r≠0:=by omega
        simpa [seed,nz] using init r hr j hj w
      · simpa [field,seed] using init 0 hp 0 hk true
    | succ t ih =>
      obtain ⟨st,clk,prev⟩:=ih (by omega)
      let y:=V x (a t);let z:=V x (a (t+1))
      have step:=steps t (by omega)
      have ck : (witness y 0 0).toNat=t:=by change (witness (V x (a t)) 0 0).toNat=t;rw [clk];simp
      have gs : slots y=slots x:=st.1
      have gy : decode y=g:=parsed sh st
      have nxt : Frozen x (a (t+1)):=by
        constructor
        · refine Eq.trans ?_ st.1;unfold slots;congr 1
          have f : field z 0 0 false=advance y 0 0 false:=step 0 hp 0 hk false
          have no : ¬((witness y 0 0).toNat< slots y ∧ 0=1+(witness y 0 0).toNat):=by omega
          change field z 0 0 false=field y 0 0 false
          simpa only [advance,Bool.false_eq_true,and_false,if_false,no] using f
        · intro r hr big j hj w;have nz : r≠0:=by omega
          have no : ¬((witness y 0 0).toNat< slots y ∧ r=1+(witness y 0 0).toNat):=by rw [gs];omega
          have f : field z r j w=advance y r j w:=step r hr j hj w
          exact (show field z r j w=field y r j w by simpa only [advance,nz,false_and,if_false,no] using f).trans (st.2 r hr big j hj w)
      refine ⟨nxt,?_,?_⟩
      · have f:=step 0 hp 0 hk true;simpa [field,advance,clk] using f
      · intro v hv vt
        have rr : 1+v< x.rows:=by unfold shaped at sh;omega
        have nz : 1+v≠0:=by omega
        by_cases eq : v=t
        · subst v
          let B:=bestWord x g (liveRow y) (rowWord y) t
          have fv (j : ℕ) (hj : j< x.k) (w : Bool) : field z (1+t) j w=B j w:=by
            have f : field z (1+t) j w=advance y (1+t) j w:=step _ rr j hj w
            unfold advance at f;rw [if_neg (by simp),ck,if_pos ⟨by simpa [gs] using hv,rfl⟩,gy] at f;exact f
          have eWord : rowWord z t=fun j w=>if j< x.k then B j w else 0:=by
            funext j w;by_cases hj : j< x.k
            · exact (if_pos hj).trans ((fv j hj w).trans (if_pos hj).symm)
            · exact (if_neg hj).trans (if_neg hj).symm
          have h0 : center z (1+t) 0=B 0 false:=fv 0 hk false
          have ok:=minimum_join_row x g (liveRow y) (rowWord y) t hn (sane x hn) size.le
            (fun p hp=>prev p (by omega) hp)
          change RowOK x g t (0≤ center z (1+t) 0) (rowWord z t)
          rw [h0,eWord];exact ok
        · have fv (j : ℕ) (hj : j< x.k) (w : Bool) : field z (1+v) j w=field y (1+v) j w:=by
            have f : field z (1+v) j w=advance y (1+v) j w:=step _ rr j hj w
            simpa only [advance,nz,false_and,if_false,ck,show ¬(t< slots y ∧ 1+v=1+t) by omega] using f
          have ew:=copyWord (x:=y) (y:=z) rfl _ _ fv
          have h0 : center z (1+v) 0=center y (1+v) 0:=fv 0 hk false
          change RowOK x g v (0≤ center z (1+v) 0) (word z (1+v))
          rw [h0,ew];exact prev v hv (by omega)
  obtain ⟨st,_,ok⟩:=inv x.rows le_rfl
  let y:=V x (a x.rows);let z:=V x m
  have gs : slots y=slots x:=st.1
  have gy : decode y=g:=parsed sh st
  have last : slots x< x.rows-1:=by unfold shaped at sh;omega
  have lr : x.rows-1< x.rows:=by omega
  refine ⟨?_,?_⟩
  · change center z (x.rows-1) 0=center x (x.rows-1) 0
    have f : field z (x.rows-1) 0 false=project y (x.rows-1) 0 false:=ending _ lr 0 hk false
    have h : ¬x.rows-1< slots y:=by rw [gs];omega
    rw [project,if_neg h] at f;exact f.trans (st.2 _ lr last 0 hk false)
  · intro r hr hv
    change r< slots x at hr
    have look (j : ℕ) (hj : j< x.k) (w : Bool) : field z r j w=field y (1+g.goal r) j w:=by
      have f : field z r j w=project y r j w:=ending _ (hr.trans size) j hj w
      rw [project,if_pos (show r< slots y by rw [gs];exact hr),gy] at f;exact f
    have ew:=copyWord (x:=y) (y:=z) rfl _ _ look
    have h0 : center z r 0=center y (1+g.goal r) 0:=look 0 hk false
    change RowOK x g _ (0≤ center z r 0) (word z r);rw [ew,h0]
    exact ok _ hv (hv.trans size)
