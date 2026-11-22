-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.independent_window_literals
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:48:54.125809+00:00
-- url     : https://prove2.me/submissions/fd835934-2355-449b-9d67-2948e45592c6

import Theorems.Thm_StableMSR_Recovery_WindowProfiles_partition_endpoint_word
import Theorems.Thm_StableMSR_Recovery_WindowCSP_pairwise_windows_glue
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
theorem solution (x : World) (W : Cluster x.n) (R : ℝ) (h : ℕ) (dm : IsMetricArray x.dist) (hr : 0≤ R) :
    let N:=greedyNet x.dist R W;let owner:=anchor x.dist W R
    ∃F : Point x.n→Partition x.n→Word,
      (∀a∈N,∀Q∈traceMenu x h (window x.dist W R a),let D:=owned owner a Q
        D.card≤ x.k → Owned x (D.biUnion id) D.card (F a Q) ∧ weight x D.card (F a Q)=cost x.dist D ∧
          ∀j< D.card,∀s,∃p∈D.biUnion id,F a Q j s=(p.val:ℤ)) ∧
      ∀P : Pick x.n,valid x W R h P →
        let S:=fun a=>(owned owner a (P a)).biUnion id
        (N : Set (Point x.n)).PairwiseDisjoint S ∧ N.biUnion S=W := by
  classical
  let N:=greedyNet x.dist R W;let own:=anchor x.dist W R
  let D (a : Point x.n) (Q : Partition x.n):=owned own a Q
  let Good (a : Point x.n) (Q : Partition x.n) (w : Word):=
    let d:=D a Q;let U:=d.biUnion id
    Owned x U d.card w ∧ weight x d.card w=cost x.dist d ∧ ∀j< d.card,∀s,∃p∈U,w j s=(p.val:ℤ)
  let F (a : Point x.n) (Q : Partition x.n) : Word:=if yes : ∃w,Good a Q w then yes.choose else RegionalBallDP.blank
  refine ⟨F,?_,?_⟩
  · intro a ha Q mem;dsimp only;intro hc
    have full:= (Finset.mem_filter.mp mem).2
    have feas : Feasible ((D a Q).biUnion id) (D a Q).card (D a Q):=by
      refine ⟨rfl,?_,?_,rfl⟩
      · intro C h;exact full.2.1 _ (Finset.mem_filter.mp h).1
      · intro C c E d ne;exact full.2.2.1 (Finset.mem_filter.mp c).1 (Finset.mem_filter.mp d).1 ne
    have ex : ∃w,Good a Q w:=WindowProfiles.partition_endpoint_word x _ _ _ hc feas
    change Good a Q (F a Q);dsimp only [F];rw [dif_pos ex];exact ex.choose_spec
  · intro P ok;dsimp only
    obtain ⟨whole,_,_⟩:=pairwise_windows_glue x W R h P dm hr ok
    let S (a : Point x.n):=(D a (P a)).biUnion id
    have inside {a : Point x.n} (ha : a∈N) {C : Cluster x.n} (hc : C∈D a (P a)) : C∈WindowCSP.output x W R P:=
      Finset.mem_biUnion.mpr ⟨a,ha,hc⟩
    constructor
    · intro a ha b hb ne;apply Finset.disjoint_left.mpr;intro p pa pb
      obtain ⟨C,ca,pc⟩:=Finset.mem_biUnion.mp pa;obtain ⟨E,eb,pe⟩:=Finset.mem_biUnion.mp pb
      by_cases eq : C=E
      · subst E;obtain ⟨_,i,hi,ai,mi⟩:=Finset.mem_filter.mp ca;obtain ⟨_,j,hj,bj,mj⟩:=Finset.mem_filter.mp eb
        exact ne (ai.symm.trans ((congrArg own (le_antisymm (mi j hj) (mj i hi))).trans bj))
      · exact Finset.disjoint_left.mp (whole.2.2.1 (inside ha ca) (inside hb eb) eq) pc pe
    · change N.biUnion S=W
      rw [←whole.2.2.2];ext p;constructor
      · intro hp;obtain ⟨a,ha,pa⟩:=Finset.mem_biUnion.mp hp;obtain ⟨C,ca,pc⟩:=Finset.mem_biUnion.mp pa
        exact Finset.mem_biUnion.mpr ⟨C,inside ha ca,pc⟩
      · intro hp;obtain ⟨C,cu,pc⟩:=Finset.mem_biUnion.mp hp;obtain ⟨a,ha,ca⟩:=Finset.mem_biUnion.mp cu
        exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_biUnion.mpr ⟨C,ca,pc⟩⟩
