-- Prove2me | solution 1 for StableMSR.Recovery.SingleSearch.singleton_search_recognizes_treewidth
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:12:17.828925+00:00
-- url     : https://prove2.me/submissions/28f782a1-9244-49bc-91b9-6359785b700d

import Definitions.Def_StableMSR_SingleVertexSearch
import Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_tight_block_progress
import Theorems.Thm_StableMSR_Recovery_SingleSearch_root_component_geometry
import Theorems.Thm_StableMSR_Recovery_DecompositionSearch_finite_decomposition_search
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (w : ℕ) :
    starts G w ↔ TreewidthLE G w := by
  classical
  constructor
  · intro allC
    apply (finite_decomposition_search G w).1.mp
    have lift (m : ℕ) : ∀ S C,one G w m S C → accepts G w m S C:=by
      induction m with
      | zero=>intro S C h;exact h.elim
      | succ m ih=>
        intro S C h;obtain ⟨sw,v,hv,ch⟩:=h
        refine ⟨insert v S,Finset.subset_insert ..,Finset.insert_subset (Finset.mem_union_right _ hv) Finset.subset_union_left,?_,⟨v,Finset.mem_inter.mpr ⟨Finset.mem_insert_self ..,hv⟩⟩,?_⟩
        · exact (Finset.card_insert_le ..).trans (by omega)
        · intro E he;exact ⟨(ch E he).1,ih _ _ (ch E he).2⟩
    intro C hC;exact lift _ _ _ (allC C hC)
  · rintro ⟨T,ft,tree,bags,td,width⟩
    letI : Fintype T:=ft
    have go (m : ℕ) : ∀S C,IsFlap G S C → boundary G C=S → (∃t,S⊆bags t) → C.card≤ m → one G w m S C:=by
      induction m with
      | zero=>intro S C hc _ _ h;have:=hc.connected.1.card_pos;omega
      | succ m ih=>
        intro S C hc eq home size
        obtain ⟨sw,v,hv,t,hbag,children⟩:=singleton_tight_block_progress td w S C hc eq home width
        refine ⟨sw,v,hv,?_⟩;intro E he
        obtain ⟨fl,sub,bw,small⟩:=children E he
        exact ⟨bw,ih _ _ fl rfl ⟨t,fun _ h=>hbag (sub h)⟩ (by omega)⟩
    intro C hc
    obtain ⟨v,hv⟩:=(mem_components.mp hc).connected.1
    obtain ⟨t,_⟩:=td.2.1 v
    exact go _ _ _ (mem_components.mp hc) ((root_component_geometry G).2.1 C hc) ⟨t,Finset.empty_subset _⟩ (Finset.card_le_univ _)
