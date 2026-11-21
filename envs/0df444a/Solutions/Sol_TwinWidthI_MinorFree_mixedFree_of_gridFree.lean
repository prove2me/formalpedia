-- Prove2me | solution 1 for TwinWidthI.MinorFree.mixedFree_of_gridFree
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:01:31.564964+00:00
-- url     : https://prove2.me/submissions/dd3c8815-a601-44e8-bae4-a1573a5040a3

import Mathlib
import Definitions.Def_TwinWidthI_MinorFree_Setting

open TwinWidthI.MinorFree in
theorem solution {n m : ℕ} (M : Matrix (Fin n) (Fin m) Bool)
    (t : ℕ) (h : ¬ TwinWidthI.GridThm.HasGridMinor M t) : TwinWidthI.GridThm.MixedFree M t := by
  intro hmix
  obtain ⟨r, c, hr, hc, hm⟩ := hmix
  apply h
  refine ⟨r, c, hr, hc, fun i j => ?_⟩
  have hv := (hm i j).1
  unfold TwinWidthI.GridThm.IsVertical at hv
  push_neg at hv
  obtain ⟨a, ha, a', ha', b, hb, hne⟩ := hv
  cases hab : M a b
  · refine ⟨a', ha', b, hb, ?_⟩
    rw [hab] at hne
    cases hab' : M a' b
    · rw [hab'] at hne
      exact absurd rfl hne
    · rfl
  · exact ⟨a, ha, b, hb, hab⟩
