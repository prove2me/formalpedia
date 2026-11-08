-- Prove2me | solution 1 for QuantileMDP.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:19:31.091143+00:00
-- url     : https://prove2.me/submissions/1155f877-bcec-4677-8cb5-c650d50a3fcd

import Mathlib
import Definitions.Def_QuantileMDP_Model
import Definitions.Def_QuantileMDP_optValue

open QuantileMDP in
theorem solution {S A : Type*} [Fintype S] [Fintype A] (M : Model S A) (T t : ℕ) (s : S) (τ : ℝ) :
    optValue M T t s τ = (⨆ a ∈ M.adm t s, optValueAct M T t s τ a) ∧
      ∃ a ∈ M.adm t s, optValueAct M T t s τ a = optValue M T t s τ := by
  have hle : ∀ a, optValueAct M T t s τ a ≤ optValue M T t s τ := by
    intro a
    unfold optValueAct optValue
    exact iSup₂_le fun π hπ => iSup_le fun _ => le_iSup₂_of_le π hπ le_rfl
  have h1 : optValue M T t s τ = ⨆ a ∈ M.adm t s, optValueAct M T t s τ a := by
    apply le_antisymm
    · unfold optValue
      refine iSup₂_le fun π hπ => ?_
      have ha : π 0 (fun _ => s) ∈ M.adm t s := hπ 0 (fun _ => s)
      refine le_iSup₂_of_le (π 0 (fun _ => s)) ha ?_
      unfold optValueAct
      exact le_iSup₂_of_le π hπ (le_iSup_of_le rfl le_rfl)
    · exact iSup₂_le fun a _ => hle a
  refine ⟨h1, ?_⟩
  obtain ⟨a0, ha0, hmax⟩ := Set.exists_max_image (M.adm t s) (optValueAct M T t s τ)
    (Set.toFinite _) (M.adm_nonempty t s)
  refine ⟨a0, ha0, ?_⟩
  rw [h1]
  exact le_antisymm (le_iSup₂_of_le a0 ha0 le_rfl) (iSup₂_le fun a ha => hmax a ha)
