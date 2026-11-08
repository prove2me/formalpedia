-- Prove2me | solution 1 for ParallelSmallWorlds.SEU.calib_mono
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:21:03.873332+00:00
-- url     : https://prove2.me/submissions/b9492979-2ea3-4ce8-ae35-815c18d48ed2

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_calib
import Definitions.Def_ParallelSmallWorlds_SEU_LikelihoodAxioms

open ParallelSmallWorlds.SEU in
theorem solution {Θ C : Type*} (W : SmallWorld Θ C)
    (hQ : MeasureTheory.IsSetAlgebra W.Q) (hL : LikelihoodAxioms W) :
    ∀ R ∈ W.Q, ∀ S ∈ W.Q, R ⊆ S → W.lik (Sum.inl S) (Sum.inl R) ∧ calib W R ≤ calib W S := by
  have mono : ∀ R ∈ W.Q, ∀ S ∈ W.Q, R ⊆ S → W.lik (Sum.inl S) (Sum.inl R) := by
    intro R hR S hS hRS
    have hD : S \ R ∈ W.Q := hQ.sdiff_mem hS hR
    have h := (hL.psw3b (S \ R) hD ∅ hQ.empty_mem R hR (Set.diff_inter_self) (Set.empty_inter R)).mp
      (hL.psw3a_nonneg (S \ R) hD)
    rwa [Set.diff_union_of_subset hRS, Set.empty_union] at h
  have hIcc : ∀ π : ℝ, Set.Icc 0 π ⊆ Set.Icc 0 1 → Set.Icc (0 : ℝ) π ∈ RefEvents :=
    fun π h => ⟨measurableSet_Icc, h⟩
  intro R hR S hS hRS
  have hSR := mono R hR S hS hRS
  refine ⟨hSR, ?_⟩
  unfold calib
  apply csInf_le_csInf
  · exact ⟨0, fun π hπ => hπ.1.1⟩
  · refine ⟨1, ⟨⟨zero_le_one, le_rfl⟩, ?_⟩⟩
    have hU := mono S hS Set.univ hQ.univ_mem (Set.subset_univ S)
    exact hL.psw1_trans (Sum.inr (Set.Icc 0 1)) (hIcc 1 le_rfl) (Sum.inl Set.univ) hQ.univ_mem
      (Sum.inl S) hS hL.psw5a.2 hU
  · intro π hπ
    refine ⟨hπ.1, ?_⟩
    exact hL.psw1_trans (Sum.inr (Set.Icc 0 π)) (hIcc π (Set.Icc_subset_Icc le_rfl hπ.1.2))
      (Sum.inl S) hS (Sum.inl R) hR hπ.2 hSR
