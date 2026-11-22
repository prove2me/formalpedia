-- Prove2me | solution 1 for StableMSR.Recovery.RegionalBallDP.disjoint_local_menus_certify_terminal
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T13:15:45.685786+00:00
-- url     : https://prove2.me/submissions/40b6c0c2-b4c8-4a01-9ee1-53c4ff4f7553

import Definitions.Def_StableMSR_LocalBallTrials
import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
private lemma add_edge {x : World} {r q : ℕ} (l : link x r q) (u : Word) :
    weight x (width x r) (splice x r q u)=weight x (width x (parent x q)) u+edgeCost x r q := by
  unfold weight edgeCost;rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro j _
  by_cases a : j<width x (parent x q)
  · have t:=lt_of_lt_of_le a l.2.2.2.2
    simp [splice,a,t,not_le.mpr a]
  · by_cases b : j<width x r <;> simp [splice,a,b,le_of_not_gt a]
private def Sound (x : World) {v : ℕ} {B : ℝ} (t : LocalTrial x v B) (r : ℕ) (u : Word) :=
  (∀j<width x r,t.region r (u j false)) ∧
  (∀j<width x r,∀l<width x r,u j false=u l false → j=l) ∧
  ∀i<x.n,t.region r (i:ℤ) → ∃j<width x r,containsPoint x u j i
private lemma routeSound {x : World} {v : ℕ} {B : ℝ} (t : LocalTrial x v B) {r : ℕ} {u : Word}
    (h : Route x r u) : t.tracked r → Sound x t r u := by
  induction h with
  | root =>
    intro _
    refine ⟨?_,?_,?_⟩
    · simp [width]
    · simp [width]
    · intro i hi hr;exact (t.emptyRoot i hi hr).elim
  | @append r q u hv l h ih =>
    intro tracked
    obtain ⟨tp,push,own,distinct,cover⟩:=t.owned r hv tracked q l
    obtain ⟨old,sep,cov⟩:=ih tp
    have lo (j : ℕ) (hj : j<width x (parent x q)) (w : Bool) : splice x r q u j w=u j w := if_pos hj
    have hi (j : ℕ) (a : width x (parent x q)≤j) (b : j<width x r) (w : Bool) :
        splice x r q u j w=payload x q j w := (if_neg (not_lt.mpr a)).trans (if_pos b)
    refine ⟨?_,?_,?_⟩
    · intro j hj;by_cases a : j<width x (parent x q)
      · rw [lo j a];exact push _ (old j a)
      · rw [hi j (by omega) hj];exact (own j (by omega) hj).1
    · intro j hj k hk eq
      by_cases a : j<width x (parent x q) <;> by_cases b : k<width x (parent x q)
      · rw [lo j a,lo k b] at eq;exact sep j a k b eq
      · rw [lo j a,hi k (by omega) hk] at eq
        exact ((own k (by omega) hk).2 (eq ▸ old j a)).elim
      · rw [hi j (by omega) hj,lo k b] at eq
        exact ((own j (by omega) hj).2 (eq.symm ▸ old k b)).elim
      · rw [hi j (by omega) hj,hi k (by omega) hk] at eq
        exact distinct j (by omega) hj k (by omega) hk eq
    · intro i hiPt region
      by_cases before : t.region (parent x q) (i:ℤ)
      · obtain ⟨j,hj,hit⟩:=cov i hiPt before
        refine ⟨j,lt_of_lt_of_le hj l.2.2.2.2,?_⟩
        unfold containsPoint;rw [lo j hj false,lo j hj true];exact hit
      · obtain ⟨j,hj,hj',hit⟩:=cover i hiPt region before
        refine ⟨j,hj',?_⟩
        unfold containsPoint;rw [hi j hj hj' false,hi j hj hj' true];exact hit
private lemma cheapPath {x : World} {v : ℕ} {B : ℝ} (t : LocalTrial x v B) (r : ℕ) (vr : vertex x r)
    (ok : t.viable r) : ∃u,Route x r u ∧ weight x (width x r) u≤t.budget r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases root : r=1
    · subst r;refine ⟨blank,.root,?_⟩;simpa [width,weight] using t.rootBudget
    · obtain ⟨q,l,viable,le⟩:=t.extendBudget r vr ok root
      obtain ⟨u,h,cheap⟩:=ih (parent x q) l.2.2.1 l.2.1 viable
      refine ⟨splice x r q u,.append vr l h,?_⟩
      rw [add_edge l u];linarith
theorem solution (x : World) (hs : shape x) (v : ℕ) (B : ℝ) (t : LocalTrial x v B) :
    vertex x v ∧ InTable x v ∧ ∃u,Route x v u ∧ weight x x.k u≤B := by
  have vt:=t.terminal
  have vr : v<x.rows := by have h:=hs.2;have a:=vt.2;omega
  refine ⟨vt,⟨vr,t.fullWidth,?_⟩,?_⟩
  · intro u route
    obtain ⟨_,separate,cover⟩:=routeSound t route t.trackedEnd
    rw [t.fullWidth] at separate cover
    exact ⟨separate,fun i hi=>cover i hi (t.fullRegion i hi)⟩
  · obtain ⟨u,path,cheap⟩:=cheapPath t v vt t.viableEnd
    rw [t.fullWidth] at cheap
    exact ⟨u,path,cheap.trans t.terminalBudget⟩

