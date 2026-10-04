-- Prove2me | solution 1 for TheoryOfGames.Decomposition.splitting_inter_union
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:38:54.063436+00:00
-- url     : https://prove2.me/submissions/cba03570-9890-482f-8639-7bc9709b1f49

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

set_option autoImplicit false

open TheoryOfGames.Decomposition in
theorem splitting_compl_aux_0f6f5dad {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J : Finset ι) (h : IsSplitting v J) : IsSplitting v Jᶜ := by
  intro S T hS hT
  rw [compl_compl] at hT
  rw [Finset.union_comm, h T S hT hS, add_comm]

open TheoryOfGames.Decomposition in
theorem splitting_inter_aux_0f6f5dad {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J' J'' : Finset ι)
    (h' : IsSplitting v J') (h'' : IsSplitting v J'') : IsSplitting v (J' ∩ J'') := by
  intro S T hS hT
  have hSJ' : S ⊆ J' := hS.trans Finset.inter_subset_left
  have hSJ'' : S ⊆ J'' := hS.trans Finset.inter_subset_right
  have h1 : S ∪ T = (S ∪ T ∩ J') ∪ (T \ J') := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have h2 : T = (T ∩ J') ∪ (T \ J') := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have hA : S ∪ T ∩ J' ⊆ J' := Finset.union_subset hSJ' Finset.inter_subset_right
  have hB : T \ J' ⊆ J'ᶜ := by
    intro x hx; rw [Finset.mem_compl]; exact (Finset.mem_sdiff.mp hx).2
  have hC : T ∩ J' ⊆ J''ᶜ := by
    intro x hx
    rw [Finset.mem_inter] at hx
    have := hT hx.1
    rw [Finset.mem_compl, Finset.mem_inter] at this
    rw [Finset.mem_compl]
    exact fun hx'' => this ⟨hx.2, hx''⟩
  have e1 := h' (S ∪ T ∩ J') (T \ J') hA hB
  have e2 := h'' S (T ∩ J') hSJ'' hC
  have e3 := h' (T ∩ J') (T \ J') Finset.inter_subset_right hB
  rw [← h2] at e3
  rw [h1, e1, e2, e3]
  ring

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (J' J'' : Finset ι)
    (h' : IsSplitting v J') (h'' : IsSplitting v J'') :
    IsSplitting v (J' ∩ J'') ∧ IsSplitting v (J' ∪ J'') := by
  refine ⟨splitting_inter_aux_0f6f5dad v J' J'' h' h'', ?_⟩
  have hc := splitting_inter_aux_0f6f5dad v J'ᶜ J''ᶜ
    (splitting_compl_aux_0f6f5dad v J' h') (splitting_compl_aux_0f6f5dad v J'' h'')
  have := splitting_compl_aux_0f6f5dad v _ hc
  rwa [← Finset.compl_union, compl_compl] at this

