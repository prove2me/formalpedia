-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.minimum_join_row
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:49:06.916896+00:00
-- url     : https://prove2.me/submissions/9f5ede76-976f-47ff-9d4a-cde3015249c8

import Theorems.Thm_StableMSR_Recovery_WindowJoins_append_radius_sum
import Theorems.Thm_StableMSR_Recovery_WindowJoins_derived_endpoint_bounds
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
private lemma chooseMin (n : ℕ) (P : ℕ→Prop) (f : ℕ→ℝ) (ex : ∃q< n,P q) :
    ∃q< n,(P q ∧ ∀r< n,P r → f q< f r ∨ f q=f r ∧ q≤ r) ∧
       ∀r< n,(P r ∧ ∀t< n,P t → f r< f t ∨ f r=f t ∧ r≤ t) → r=q :=by
  classical
  let S:=(Finset.range n).filter P
  obtain ⟨i,hi,pi⟩:=ex
  have sn : S.Nonempty:=⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,pi⟩⟩
  obtain ⟨u,hu,best⟩:=Finset.exists_min_image S f sn
  let D:=S.filter (fun q=>f q=f u)
  have dn : D.Nonempty:=⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩
  let q:=D.min' dn
  obtain ⟨qs,qe⟩:=Finset.mem_filter.mp (D.min'_mem dn)
  obtain ⟨qr,qp⟩:=Finset.mem_filter.mp qs
  have qn:=Finset.mem_range.mp qr
  have win (r) (hr : r< n) (pr : P r) : f q< f r ∨ f q=f r ∧ q≤ r:=by
    have rs : r∈S:=Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,pr⟩
    change f q=f u at qe
    rcases lt_or_eq_of_le (qe.le.trans (best r rs)) with lt|eq
    · exact Or.inl lt
    · exact Or.inr ⟨eq,D.min'_le _ (Finset.mem_filter.mpr ⟨rs,eq.symm.trans qe⟩)⟩
  refine ⟨q,qn,⟨qp,win⟩,?_⟩;intro r hr h
  rcases win r hr h.1 with lt|⟨eq,le⟩ <;> rcases h.2 q qn qp with gt|⟨eq',ge⟩
  · linarith
  · linarith
  · linarith
  · omega
theorem solution (x : World) (g : Rules) (on : ℕ→Prop) (T : ℕ→Word) (v : ℕ)
    (hn : 0< x.n) (s : Sane x g) (size : g.size≤ x.rows) (prev : ∀p< v,RowOK x g p (on p) (T p)) :
    let B:=bestWord x g on T v
    RowOK x g v (0≤ B 0 false) (fun j w=>if j< x.k then B j w else 0) := by
  classical
  let E:=eligible g on v
  let C:=candidate x.k g T v
  let f:=fun q=>weight x (g.len v) (C q)
  have realises {q} (hq : E q) : Derives x.k g v (C q):=by
    by_cases yes : g.fork q
    · obtain ⟨jc,la,ra⟩:=hq.2 yes
      simpa [C,candidate,yes] using Derives.join hq.1 yes jc ((prev _ jc.1).1 la) ((prev _ jc.2.1).1 ra)
    · simpa [C,candidate,yes] using (Derives.leaf (k:=x.k) hq.1 yes)
  have compete {u} (der : Derives x.k g v u) : ∃q< x.rows,E q ∧ f q≤ weight x (g.len v) u:=by
    cases der with
    | @leaf _ q ar nf =>
      exact ⟨q,ar.1.trans_le size,⟨ar,fun t=>(nf t).elim⟩,by simp [f,C,candidate,nf]⟩
    | @join _ q l r ar yes jc dl dr =>
      obtain ⟨la,lp⟩:=(prev _ jc.1).2 _ dl
      obtain ⟨ra,rp⟩:=(prev _ jc.2.1).2 _ dr
      refine ⟨q,ar.1.trans_le size,⟨ar,fun _=>⟨jc,la,ra⟩⟩,?_⟩
      have he:=jc.2.2
      have cap:=s.1 v
      simp only [f,C,candidate,if_pos yes,←he]
      rw [append_radius_sum x _ _ (by omega),append_radius_sum x _ _ (by omega)]
      exact add_le_add lp rp
  by_cases ex : ∃q< x.rows,E q
  · obtain ⟨q,hq,win,uniq⟩:=chooseMin x.rows E f ex
    have ww : winner x g on T v q:=win
    have value : bestWord x g on T v=C q:=by
      funext j w;unfold bestWord;rw [if_pos ex,Finset.sum_eq_single q]
      · exact if_pos ww
      · intro r hr ne;exact if_neg (fun z=>ne (uniq r (Finset.mem_range.mp hr) z))
      · exact fun no=>(no (Finset.mem_range.mpr hq)).elim
    have d:=realises win.1
    obtain ⟨sane,pad⟩:=derived_endpoint_bounds x g s hn v _ d
    have eq : (fun j w=>if j< x.k then bestWord x g on T v j w else 0)=C q:=by
      funext j w;rw [value];by_cases hj : j< x.k
      · simp [hj]
      · rw [if_neg hj];exact (pad j (by have:=s.1 v;omega) w).symm
    dsimp only;rw [eq,value]
    refine ⟨fun _=>d,?_⟩;intro u du
    obtain ⟨r,hr,pr,cp⟩:=compete du
    rcases win.2 r hr pr with lt|⟨same,_⟩
    · exact ⟨(sane 0 false).1,lt.le.trans cp⟩
    · exact ⟨(sane 0 false).1,same.le.trans cp⟩
  · have off : ¬0≤ bestWord x g on T v 0 false:=by simp [bestWord,show ¬∃q< x.rows,eligible g on v q from ex]
    refine ⟨fun h=>(off h).elim,?_⟩;intro u d
    obtain ⟨r,hr,p,_⟩:=compete d;exact (ex ⟨r,hr,p⟩).elim
