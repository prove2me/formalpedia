-- Prove2me | solution 1 for TroppMatrixConcentration.lieb_concavity
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-07T14:44:34.572917+00:00
-- url     : https://prove2.me/submissions/a0b8acd4-3d99-4f69-8f5b-7dd0414c18fa

import Theorems.Thm_TroppMatrixConcentration_ch8_entropy_joint_convex
import Theorems.Thm_TroppMatrixConcentration_ch8_variational_trace_exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped Matrix.Norms.L2Operator ComplexOrder
open TroppMatrixConcentration
set_option autoImplicit false

theorem solution {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef}
      (fun A => traceExp (H + matrixLog A)) := by
  have hj := ch8_entropy_joint_convex (d := d)
  have hc : Convex ℝ {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef} := by
    intro A hA B hB a b ha hb hab
    exact (hj.1 (show (A,A) ∈ _ from ⟨hA,hA⟩)
      (show (B,B) ∈ _ from ⟨hB,hB⟩) ha hb hab).1
  refine ⟨hc, ?_⟩
  intro A hA B hB a b ha hb hab
  obtain ⟨T,hT,hTA⟩ := (ch8_variational_trace_exp H A hH hA).1
  obtain ⟨U,hU,hUB⟩ := (ch8_variational_trace_exp H B hH hB).1
  have hAB := hc hA hB ha hb hab
  have hTU := hc hT hU ha hb hab
  have hentropy := hj.2 (show (T,A) ∈ _ from ⟨hT,hA⟩)
    (show (U,B) ∈ _ from ⟨hU,hB⟩) ha hb hab
  change ch8_relativeEntropy (a • T + b • U) (a • A + b • B) ≤
    a * ch8_relativeEntropy T A + b * ch8_relativeEntropy U B at hentropy
  have hmax := (ch8_variational_trace_exp H (a • A + b • B) hH hAB).2
    ⟨a • T + b • U,hTU,rfl⟩
  have htrace (C D : Matrix (Fin d) (Fin d) ℂ) :
      (Matrix.trace (a • C + b • D)).re = a * (Matrix.trace C).re + b * (Matrix.trace D).re := by
    simp
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, htrace, htrace] at hmax
  change a * traceExp (H + matrixLog A) + b * traceExp (H + matrixLog B) ≤ _
  rw [hTA,hUB]
  nlinarith
