-- Prove2me | solution 1 for PGDRevision20261113.loss_matched_one_step
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T09:22:49.42545+00:00
-- url     : https://prove2.me/submissions/038295d7-dff8-4dd8-a9d0-39fac2d258d8

import Definitions.Def_PGDRevision20261113_Examples
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open PGDRevision20261113

theorem solution : LossMatchedOneStepClaim := by
  intro P p hP hmatched ell x ht
  rcases hP with ⟨hne, hopen, hord, hf, hg, hphi, hp, hcurv, hsurj⟩
  have hx0 : x 0 ∈ P.domain := ht.1 0 (by norm_num)
  have hx1 : x 1 ∈ P.domain := ht.1 1 (by norm_num)
  have hfd := (hf.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hx1)
  have hgd := (hg.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hx1)
  have hd : HasDerivAt (objective P ell)
      (deriv P.f (x 1) + deriv P.g (x 1) + ell) (x 1) := by
    convert (hfd.hasDerivAt.add hgd.hasDerivAt).add
      ((hasDerivAt_id (x 1)).const_mul ell) using 1 <;> first | rfl | simp [objective]
  have hu : p * deriv P.phi (x 1) + deriv P.g (x 1) =
      p * deriv P.phi (x 0) - deriv P.f (x 0) - ell := by
    simpa using ht.2 0 (by norm_num)
  rw [hmatched (x 1) hx1, hmatched (x 0) hx0] at hu
  unfold objectiveDerivative
  rw [hd.deriv]
  linarith
