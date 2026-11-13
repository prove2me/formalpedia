-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.quasipoint_regularization_membership
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:34:57.850764+00:00
-- url     : https://prove2.me/submissions/ed9c3fe8-ef41-4a4e-8696-c7a8e9ad3de4

import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_upward_and_meet_closed
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_quasipoint_nonmember_has_disjoint_member
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
noncomputable section
open Set TopologicalSpace
universe u

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {M : Type u} [TopologicalSpace M]
    (B : StoneSpectrum (Opens M)) (U : Opens M) :
    U ∈ B.val ↔ regularizeOpen U ∈ B.val := by
  classical
  have hu := quasipoint_upward_and_meet_closed B.val B.property
  constructor
  · intro hU
    apply hu.1 U hU (regularizeOpen U)
    exact U.isOpen.subset_interior_closure
  · intro hU
    by_contra hn
    obtain ⟨V,hV,hVU⟩ := quasipoint_nonmember_has_disjoint_member B.val B.property U hn
    have hdis : Disjoint (V : Set M) (U : Set M) := by
      apply disjoint_iff_inter_eq_empty.mpr
      exact congrArg (fun W : Opens M => (W : Set M)) hVU
    have hdisj : Disjoint (V : Set M) (regularizeOpen U : Set M) :=
      (hdis.closure_right V.isOpen).mono_right interior_subset
    have hz : V ⊓ regularizeOpen U = ⊥ := by
      apply Opens.ext
      exact disjoint_iff_inter_eq_empty.mp hdisj
    have hh := hu.2 V hV (regularizeOpen U) hU
    rw [hz] at hh
    exact B.property.1.2.1 hh
