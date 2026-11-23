-- Prove2me | solution 1 for StableMSR.Recovery.SingleSearch.singleton_tight_block_progress
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:13:20.166625+00:00
-- url     : https://prove2.me/submissions/d55dff2b-5699-4be3-a5e1-e93340205ef1

import Definitions.Def_StableMSR_SingleVertexSearch
import Theorems.Thm_StableMSR_Recovery_SingleSearch_deletion_piece_geometry
import Theorems.Thm_StableMSR_Recovery_DecompositionSearch_tight_block_progress
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
theorem solution {V T : Type} [Fintype V] [DecidableEq V] [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T→Finset V}
    (htd : IsTreeDecomposition G tree bags) (w : ℕ) (S C : Finset V)
    (hc : IsFlap G S C) (tight : boundary G C=S) (home : ∃t,S⊆bags t) (width : ∀t,(bags t).card≤ w+1) :
    S.card≤ w ∧ ∃v∈C,∃t,insert v S⊆bags t ∧ ∀E∈children G (insert v S) C,
      IsFlap G (boundary G E) E ∧ boundary G E⊆insert v S ∧ (boundary G E).card≤ w ∧ E.card< C.card := by
  classical
  obtain ⟨T0,sT,tSC,tc,⟨v,hv⟩,sw,⟨t,ht⟩,_,old⟩:=tight_block_progress htd S C w hc tight home width
  have vT:= (Finset.mem_inter.mp hv).1
  have vC:= (Finset.mem_inter.mp hv).2
  have vs : v∉S:=fun s=>Finset.disjoint_left.mp hc.avoids s vC
  let B:=insert v S
  have BT : B⊆T0:=Finset.insert_subset vT sT
  have SB : S⊆B:=Finset.subset_insert _ _
  have BC : B⊆S∪C:=fun _ hv=>tSC (BT hv)
  have kk:=deletion_piece_geometry G S C B hc SB BC
  refine ⟨sw,v,vC,t,fun _ h=>ht (BT h),?_⟩
  intro E he
  obtain ⟨fl,dis,eb,_⟩:=kk.2.2.1 E he
  have small : E.card< C.card:=by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨(mem_children.mp he).2,?_⟩
    intro eq;have vm : v∈E:=eq.symm ▸ vC
    exact Finset.disjoint_left.mp dis vm (Finset.mem_insert_self ..)
  refine ⟨fl,eb,?_,small⟩
  by_cases slack : S.card< w
  · have h:=Finset.card_le_card eb;have sz : B.card=S.card+1:=Finset.card_insert_of_notMem vs
    omega
  · have sz : B.card=S.card+1:=Finset.card_insert_of_notMem vs
    have same : B=T0:=Finset.eq_of_subset_of_card_le BT (by omega)
    change E∈children G B C at he
    rw [same] at he
    exact (old E he).2.2.1
