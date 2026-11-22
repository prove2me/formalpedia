-- Prove2me | solution 1 for StableMSR.Recovery.WindowGeometry.canonical_net_prefix
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T23:31:59.628627+00:00
-- url     : https://prove2.me/submissions/4c9e19dd-54b8-4373-933d-72b351fb39d6

import Definitions.Def_StableMSR_RegionAtlas
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
theorem solution {n : ℕ} (d : Point n→Point n→ℝ) (R : ℝ) (W : Cluster n) (p : Point n) :
    let U:=W.filter (fun i=>i.val< p.val);let N:=Supplement.greedyNet d R U
    Supplement.greedyNet d R (W.filter (fun i=>i.val< p.val+1))=
      if p∈W ∧ ∀s∈N,2*R< d p s then insert p N else N := by
  classical
  let U:=W.filter (fun i=>i.val< p.val)
  let U':=W.filter (fun i=>i.val< p.val+1)
  let N:=Supplement.greedyNet d R U
  change Supplement.greedyNet d R U'=if p∈W ∧ ∀s∈N,2*R< d p s then insert p N else N
  by_cases inside : p∈W
  · have ep : U'=insert p U:=by
      ext i;simp only [U',U,Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨h,lo⟩;by_cases e : i=p
        · exact Or.inl e
        · exact Or.inr ⟨h,by have : i.val≠p.val:=fun eq=>e (Fin.ext eq);omega⟩
      · rintro (rfl|⟨h,lo⟩)
        · exact ⟨inside,by omega⟩
        · exact ⟨h,by omega⟩
    let L:=U.sort (·≤·)
    have np : p∉L:=by simp [L,U]
    have nodup : (L++[p]).Nodup:=by
      rw [List.nodup_append];exact ⟨U.sort_nodup _,by simp,by
        intro a ha b hb eq
        subst b
        have e : a=p:=by simpa using hb
        exact np (e ▸ ha)⟩
    have ordered : (L++[p]).Pairwise (·≤·):=by
      apply List.pairwise_append.mpr;refine ⟨U.pairwise_sort _,by simp,?_⟩
      intro a ha b hb;have beq : b=p:=by simpa using hb
      rw [beq];exact ((Finset.mem_filter.mp (Finset.mem_sort _ |>.mp ha)).2).le
    have bits : (L++[p]).toFinset=U':=by simp [L,ep,Finset.union_comm]
    have sort : U'.sort (·≤·)=L++[p]:=by rw [← bits];exact (List.toFinset_sort _ nodup).mpr ordered
    unfold Supplement.greedyNet;rw [sort,List.foldl_append];simp [N,L,Supplement.greedyNet,inside]
  · have ep : U'=U:=by
      ext i;simp only [U',U,Finset.mem_filter]
      constructor
      · rintro ⟨wi,low⟩;refine ⟨wi,?_⟩
        have ne : i.val≠p.val:=fun eq=>inside (Fin.ext eq ▸ wi);omega
      · rintro ⟨wi,low⟩;exact ⟨wi,by omega⟩
    rw [ep,if_neg (fun c=>inside c.1)]
