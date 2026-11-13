-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P20.regularization_preserves_meet
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:33:06.760212+00:00
-- url     : https://prove2.me/submissions/28063904-9a06-44dd-9d8d-f5dcd5288e27

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
noncomputable section
open Set TopologicalSpace
universe u

open QAlgorithms.Papers.Independent.Intakethird100.P20

theorem solution {M : Type u} [TopologicalSpace M] (U V : Opens M) :
    regularizeOpen (U ⊓ V) = regularizeOpen U ⊓ regularizeOpen V := by
  have hj (W : Opens M) : regularizeOpen W = Wᶜᶜ := by
    ext x
    simp [regularizeOpen,Opens.coe_compl_eq_interior_compl,interior_compl]
  rw [hj,hj,hj]
  exact compl_compl_inf_distrib U V
