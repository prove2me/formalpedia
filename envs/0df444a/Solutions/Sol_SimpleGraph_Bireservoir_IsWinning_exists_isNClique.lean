-- Prove2me | solution 1 for SimpleGraph.Bireservoir.IsWinning.exists_isNClique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:31.833967+00:00
-- url     : https://prove2.me/submissions/b4a0a5b7-eee5-4236-af33-c496315522a6

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_Bireservoir_card_redPivot_pool_add_card_bluePivot_pool
public import Theorems.Thm_SimpleGraph_IsClique_exists_isNClique_subset
public import Theorems.Thm_SimpleGraph_Bireservoir_IsWinning_exists_pivot
public import Theorems.Thm_SimpleGraph_RamseyBound_exists_isNClique_subset


set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Bireservoir
variable {G}
variable (S : G.Bireservoir)
variable {S}
namespace SimpleGraph.Bireservoir
namespace IsWinning
theorem _root_.solution {R : ℕ → ℕ → ℕ} {r s : ℕ} (hR : IsPascal R)
    (hS : S.IsWinning R r s) : (∃ t, G.IsNClique r t) ∨ ∃ t, Gᶜ.IsNClique s t := by
  classical
  induction hn : #S.pool using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hr : r ≤ #S.red
    · obtain ⟨t, -, ht⟩ := S.isClique_red.exists_isNClique_subset hr
      exact .inl ⟨t, ht⟩
    by_cases hs : s ≤ #S.blue
    · obtain ⟨t, -, ht⟩ := S.isClique_blue.exists_isNClique_subset hs
      exact .inr ⟨t, ht⟩
    obtain ⟨v, hv, h | h⟩ := hS.exists_pivot hR (by omega) (by omega)
    · refine ih _ ?_ h rfl
      have := S.card_redPivot_pool_add_card_bluePivot_pool hv
      omega
    · refine ih _ ?_ h rfl
      have := S.card_redPivot_pool_add_card_bluePivot_pool hv
      omega
end IsWinning
end SimpleGraph.Bireservoir
