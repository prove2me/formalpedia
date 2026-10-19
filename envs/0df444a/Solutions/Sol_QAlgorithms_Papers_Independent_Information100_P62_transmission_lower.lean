-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.transmission_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:05:24.525505+00:00
-- url     : https://prove2.me/submissions/c5610c10-ab71-4495-976e-77041bffc021

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P62
noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.21, Remark 3.2: downward closure. -/


theorem solution [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A B : Shape) (hA : Valid A)
    (hB : Transmits F B) (h : Embeds A B) : Transmits F A := by
  obtain ⟨_, f, ⟨hfi, hfm, hfs⟩, hf⟩ := hB
  obtain ⟨g, hgi, hgm, hgs⟩ := h
  refine ⟨hA, f.comp g, ⟨hfi.comp hgi, ?_, ?_⟩, ?_⟩
  · intro x y; simp [hgm, hfm]
  · intro x; simp [hgs, hfs]
  · intro X s hs
    simp only [LinearMap.comp_apply]
    set P := f 1 with hP
    have key : ∀ Y, f Y * (P * s * P) = (P * s * P) * f Y := fun Y => hf Y s hs
    have h1 : f (g 1) * P = f (g 1) := by rw [hP, ← hfm, mul_one]
    have h2 : P * f (g 1) = f (g 1) := by rw [hP, ← hfm, one_mul]
    have h3 : f (g 1) * f (g X) = f (g X) := by rw [← hfm, ← hgm, one_mul]
    have h4 : f (g X) * f (g 1) = f (g X) := by rw [← hfm, ← hgm, mul_one]
    have e : f (g 1) * s * f (g 1) = f (g 1) * (P * s * P) * f (g 1) := by
      rw [show f (g 1) * (P * s * P) * f (g 1) = (f (g 1) * P) * s * (P * f (g 1)) by
        simp only [mul_assoc], h1, h2]
    rw [e]
    have kq := key (g 1)
    have kx := key (g X)
    generalize P * s * P = M at kq kx ⊢
    calc f (g X) * (f (g 1) * M * f (g 1))
        = (f (g X) * f (g 1)) * M * f (g 1) := by simp only [mul_assoc]
      _ = M * f (g X) * f (g 1) := by rw [h4, kx]
      _ = M * f (g X) := by rw [mul_assoc, h4]
      _ = f (g 1) * f (g X) * M := by rw [h3, kx]
      _ = f (g 1) * (M * f (g X)) := by rw [mul_assoc, kx]
      _ = f (g 1) * M * (f (g 1) * f (g X)) := by rw [h3, mul_assoc]
      _ = f (g 1) * M * f (g 1) * f (g X) := by rw [mul_assoc (f (g 1) * M)]


end

