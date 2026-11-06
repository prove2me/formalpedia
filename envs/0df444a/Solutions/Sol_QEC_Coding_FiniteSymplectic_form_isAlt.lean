-- Prove2me | solution 1 for QEC.Coding.FiniteSymplectic.form_isAlt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:33:26.262723+00:00
-- url     : https://prove2.me/submissions/7d2c5876-2e85-4d61-b972-b9e6cac1f0a2

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u v
open QEC.Coding.FiniteSymplectic
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]
namespace QEC.Coding.FiniteSymplectic
theorem _root_.solution : (form (F := F) (ι := ι)).IsAlt := by
  intro v
  change symplecticForm v v = 0
  rw [symplecticForm]
  apply Finset.sum_eq_zero
  intro i _hi
  exact sub_eq_zero.mpr (mul_comm _ _)
end QEC.Coding.FiniteSymplectic
