-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.append_disjoint_owned_covers
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:49:07.001418+00:00
-- url     : https://prove2.me/submissions/863b2699-d47e-489f-a4d2-53b30a2a076e

import Theorems.Thm_StableMSR_Recovery_WindowJoins_append_radius_sum
import Definitions.Def_StableMSR_WindowJoinTemplates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery.TreeDP StableMSR.Recovery.Supplement StableMSR.Recovery.RegionalSeeds
theorem solution (x : World) (W U : Cluster x.n) (a b : ℕ) (h : a+b≤ x.k) (dis : Disjoint W U)
    (L R : Word) (hl : Owned x W a L) (hr : Owned x U b R) :
    Owned x (W∪U) (a+b) (appendWords x.k a (a+b) L R) ∧
    weight x (a+b) (appendWords x.k a (a+b) L R)=weight x a L+weight x b R := by
  let F:=appendWords x.k a (a+b) L R
  have left (j) (hj : j< a) (s : Bool) : F j s=L j s:=if_pos hj
  have after (i) (hi : i< b) (s : Bool) : F (a+i) s=R i s:=by
    have off : shift x.k (a+i) a=i:=by
      unfold shift;rw [Finset.sum_eq_single i]
      · simp
      · intro t _ ne;exact if_neg (fun e=>ne (Nat.add_left_cancel e))
      · exact fun no=>(no (Finset.mem_range.mpr (by omega))).elim
    unfold F appendWords;rw [if_neg (by omega),if_pos (by omega),off]
  have right (j) (low : a≤ j) (high : j< a+b) (s : Bool) : F j s=R (j-a) s:=by
    have eq:=after (j-a) (by omega) s;simpa only [Nat.add_sub_of_le low] using eq
  have diff {j l} (hj : j< a) (hidx : l< b) : L j false≠R l false:=by
    obtain ⟨p,pW,ep⟩:=hl.1 j hj
    obtain ⟨q,qU,eq⟩:=hr.1 l hidx
    intro same;have cast : (p.val:ℤ)=(q.val:ℤ):=ep.symm.trans (same.trans eq)
    have pq : p=q:=Fin.ext (by exact_mod_cast cast)
    exact Finset.disjoint_left.mp dis pW (pq ▸ qU)
  refine ⟨⟨?_,?_,?_⟩,append_radius_sum x a b h L R⟩
  · intro j hj;by_cases low : j< a
    · obtain ⟨p,hp,eq⟩:=hl.1 j low;exact ⟨p,Finset.mem_union_left _ hp,(left j low false).trans eq⟩
    · obtain ⟨p,hp,eq⟩:=hr.1 (j-a) (by omega);exact ⟨p,Finset.mem_union_right _ hp,(right j (by omega) hj false).trans eq⟩
  · intro j hj l h_l eq;change F j false=F l false at eq
    by_cases one : j< a <;> by_cases two : l< a
    · rw [left j one false,left l two false] at eq;exact hl.2.1 j one l two eq
    · rw [left j one false,right l (by omega) h_l false] at eq;exact (diff one (by omega) eq).elim
    · rw [right j (by omega) hj false,left l two false] at eq;exact (diff two (by omega) eq.symm).elim
    · rw [right j (by omega) hj false,right l (by omega) h_l false] at eq
      have:=hr.2.1 (j-a) (by omega) (l-a) (by omega) eq;omega
  · intro p hp;rcases Finset.mem_union.mp hp with hW|hU
    · obtain ⟨j,hj,hit⟩:=hl.2.2 p hW;refine ⟨j,by omega,?_⟩
      change contains x F j p;unfold contains RegionalBallDP.containsPoint;rw [left j hj false,left j hj true];exact hit
    · obtain ⟨j,hj,hit⟩:=hr.2.2 p hU;refine ⟨a+j,by omega,?_⟩
      change contains x F (a+j) p;unfold contains RegionalBallDP.containsPoint;rw [after j hj false,after j hj true];exact hit
