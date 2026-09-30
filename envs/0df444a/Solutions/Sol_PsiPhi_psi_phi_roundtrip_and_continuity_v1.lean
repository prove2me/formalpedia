-- Prove2me | solution 1 for PsiPhi.psi_phi_roundtrip_and_continuity_v1
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-30T06:20:58.393414+00:00
-- url     : https://prove2.me/submissions/dc03d644-14f6-4e89-a8ed-372207c18f67

import Definitions.Def_PsiPhi
set_option autoImplicit false
open PsiPhi

theorem solution : ¬ (∀ (n : ℕ) (x : {x : ℝ // x < (n : ℝ) + 1}) (y : ℝ),
    phi n (psi n x.1) = x.1 ∧
      psi n (phi n y) = y ∧
      psi n x.1 < (n : ℝ) + 1 ∧
      phi n y < (n : ℝ) + 1 ∧
      ContinuousOn (psi n) (Set.Iio ((n : ℝ) + 1)) ∧
      Continuous (phi n)) := by
  intro h
  have hf := (h 0 ⟨3/4, by norm_num⟩ 0).2.2.1
  norm_num [psi] at hf
