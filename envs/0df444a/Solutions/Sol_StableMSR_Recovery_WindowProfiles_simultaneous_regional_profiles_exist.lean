-- Prove2me | solution 1 for StableMSR.Recovery.WindowProfiles.simultaneous_regional_profiles_exist
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:16:25.647817+00:00
-- url     : https://prove2.me/submissions/7cf08efe-741b-4caa-8570-72a591bee111

import Theorems.Thm_StableMSR_Recovery_WindowProfiles_bounded_width_profile_witnesses
import Definitions.Def_StableMSR_WindowProfiles
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.Supplement StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

private lemma nextSlot {n a b i : ℕ} (hi : i< n) (h : a< b) (j : ℕ) : a*n+i< b*n+j:=by
  have h₁ : a*n+i<(a+1)*n:=by rw [Nat.succ_mul];omega
  exact h₁.trans_le ((Nat.mul_le_mul_right n h).trans (Nat.le_add_right ..))
private lemma injSlot {n p q a b : ℕ} (a0 : a< n) (b0 : b< n) (eq : p*n+a=q*n+b) : p=q ∧ a=b:=by
  have h : p=q:=by
    rcases lt_trichotomy p q with lo|same|hi
    · exact (ne_of_lt (nextSlot a0 lo b) eq).elim
    · exact same
    · exact (ne_of_lt (nextSlot b0 hi a) eq.symm).elim
  subst q;exact ⟨rfl,Nat.add_left_cancel eq⟩
theorem solution (x : World) (e : ℚ) (hk : 1≤ x.k) (hn : x.k< x.n) (dm : IsMetricArray x.dist) :
    ∃m : Mem,Profiles x e m := by
  classical
  let T:=Fin x.rows × Fin x.n × Fin (x.k+1)
  let Wish (I : T) (v : RegionalBallDP.Word) :=
    let W:=piece x I.1.val I.2.1.val;let c:=I.2.2.val;let R:=scale x I.1.val
    Owned x W c v ∧ (∀j< c,∀s,∃p∈W,v j s=(p.val:ℤ)) ∧
      (I.2.1.val∈keys x I.1.val → 0< R →
        RobertsonSeymour1986.GM5.TreewidthLE (interactionGraph x.dist R W) (widthBound (e:ℝ)) →
        ∀P : Pick x.n,valid x W R (budget (e:ℝ)) P → number x W R P=c →
          RegionalBallDP.weight x c v≤ WindowCSP.price x W R P)
  let atIndex (I : T × Fin x.k × Bool):=addr x.k (index x.n I.1.1.val I.1.2.1.val I.1.2.2.val) I.2.1.val + I.2.2.toNat
  have inject : Function.Injective atIndex:=by
    rintro ⟨⟨u,i,c⟩,j,s⟩ ⟨⟨U,I,C⟩,J,S⟩ eq
    change 3+2*(index x.n u.val i.val c.val*x.k+j.val)+s.toNat=3+2*(index x.n U.val I.val C.val*x.k+J.val)+S.toNat at eq
    have same : s=S ∧ index x.n u.val i.val c.val*x.k+j.val=index x.n U.val I.val C.val*x.k+J.val:=by
      cases s <;> cases S <;> simp [Bool.toNat] at eq ⊢ <;> omega
    have pair:=injSlot j.isLt J.isLt same.2
    have cc : c.val< x.n:=by omega
    have CC : C.val< x.n:=by omega
    have tri:=injSlot cc CC pair.1
    have duo:=injSlot i.isLt I.isLt tri.1
    exact Prod.ext (Prod.ext (Fin.ext duo.1) (Prod.ext (Fin.ext duo.2) (Fin.ext tri.2))) (Prod.ext (Fin.ext pair.2) same.1)
  let val (I : T × Fin x.k × Bool) : ℤ:=if a : ∃v,Wish I.1 v then
     if I.2.1.val< I.1.2.2.val then a.choose I.2.1.val I.2.2 else 0 else -1
  let m : Mem:=Function.extend atIndex val (fun _=>0)
  let y:=replace x m
  have read (I : T) (j : Fin x.k) (s : Bool) :
      RegionalBallDP.field y (index x.n I.1.val I.2.1.val I.2.2.val) j.val s=val (I,j,s):=by
    have h:=inject.extend_apply val (fun _=>0) (I,j,s)
    cases s <;> exact h
  let zero : Fin x.k:=⟨0,hk⟩
  have live (I : T) : active y I.1 I.2.1 I.2.2 ↔ ∃v,Wish I v:=by
    change (0≤ RegionalBallDP.field y (index x.n I.1.val I.2.1.val I.2.2.val) zero.val false) ↔ _
    rw [read I zero false]
    by_cases h : ∃v,Wish I v
    · refine iff_of_true ?_ h
      dsimp only [val];rw [dif_pos h]
      split
      next low => obtain ⟨q,_,eq⟩:=h.choose_spec.2.1 0 low false;rw [eq];omega
      next _ => omega
    · simp [val,h]
  have agrees (I : T) (h : ∃v,Wish I v) (j : ℕ) (hj : j< I.2.2.val) (s : Bool) :
      token y I.1 I.2.1 I.2.2 j s=h.choose j s:=by
    let J : Fin x.k:=⟨j,by have cap:=I.2.2.isLt;omega⟩
    obtain ⟨q,_,eq⟩:=h.choose_spec.2.1 j hj s
    change RegionalBallDP.legalize x.n (RegionalBallDP.field y (index x.n I.1.val I.2.1.val I.2.2.val) J.val s)=_
    rw [read I J s];dsimp only [val];rw [dif_pos h,if_pos hj,eq]
    exact if_pos ⟨by omega,by exact_mod_cast q.isLt⟩
  refine ⟨m,?_⟩;intro u hu i hi
  let cell (c : ℕ) (hc : c≤ x.k) : T:=⟨⟨u,hu⟩,⟨i,hi⟩,⟨c,by omega⟩⟩
  constructor
  · intro c hc on
    let I:=cell c hc
    have h:=(live I).mp on
    have sound:=h.choose_spec.1
    have eq:=agrees I h
    change Owned x (piece x u i) c (token y u i c)
    refine ⟨?_,?_,?_⟩
    · intro j hj;rw [eq j hj false];exact sound.1 j hj
    · intro j hj t ht same;rw [eq j hj false,eq t ht false] at same;exact sound.2.1 j hj t ht same
    · intro q hq;obtain ⟨j,hj,hit⟩:=sound.2.2 q hq
      refine ⟨j,hj,?_⟩;unfold contains RegionalBallDP.containsPoint at hit ⊢
      rw [eq j hj false,eq j hj true];exact hit
  constructor
  · intro unused
    apply (live (cell 0 (by omega))).mpr
    refine ⟨RegionalBallDP.blank,?_⟩
    dsimp only [Wish,cell]
    refine ⟨⟨fun j hj=>(Nat.not_lt_zero j hj).elim,fun j hj=>(Nat.not_lt_zero j hj).elim,?_⟩,
      fun j hj=>(Nat.not_lt_zero j hj).elim,fun imp=>(unused imp).elim⟩
    intro p mem;have eq:=(Finset.mem_filter.mp mem).2
    exact (unused (Finset.mem_image.mpr ⟨p,Finset.mem_univ _,eq⟩)).elim
  · intro used pos tw P validP
    dsimp only;intro hc
    let W:=piece x u i;let R:=scale x u;let c:=number x W R P;let I:=cell c hc
    obtain ⟨plan,_,find⟩:=bounded_width_profile_witnesses x W R (budget (e:ℝ)) (widthBound (e:ℝ)) dm pos.le tw
    obtain ⟨t,_,v,_,owns,price,legal,minimal⟩:=find c hc P validP rfl
    have h : ∃w,Wish I w:=⟨v,owns,legal,fun _ _ _ Q good count=>price.le.trans (minimal Q good count)⟩
    refine ⟨(live I).mpr h,?_⟩
    have eq : RegionalBallDP.weight x c (token y u i c)=RegionalBallDP.weight x c h.choose:=by
      unfold RegionalBallDP.weight;apply Finset.sum_congr rfl;intro j _
      by_cases small : j< c
      · rw [if_pos small,if_pos small,agrees I h j small false,agrees I h j small true]
      · rw [if_neg small,if_neg small]
    exact eq.le.trans (h.choose_spec.2.2 used pos tw P validP rfl)

