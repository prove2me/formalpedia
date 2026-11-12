-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P44.figureOfMerit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T19:54:22.249242+00:00
-- url     : https://prove2.me/submissions/22fd7bcf-404d-435a-929d-bb587840f4a0

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P44

open scoped BigOperators ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Frontier18.P11 (complexMatrix)

namespace Aux_FOM44

theorem foldr_le (l : List ℝ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ a ∈ l, a ≤ c) :
    l.foldr max 0 ≤ c := by
  induction l with
  | nil => exact hc
  | cons a l ih =>
    show max a (l.foldr max 0) ≤ c
    exact max_le (h a List.mem_cons_self) (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

theorem foldr_nonneg (l : List ℝ) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => exact le_refl 0
  | cons a l ih =>
    show 0 ≤ max a (l.foldr max 0)
    exact le_max_of_le_right ih

end Aux_FOM44

open QAlgorithms.Papers.Independent.Extend50.P44 in
theorem solution (N D Sc Sr : ℕ) (hN : 0 < N) (hD : D ≤ N)
    (hc : Sc ≤ N) (hr : Sr ≤ N) (A : Matrix (Fin N) (Fin N) ℝ) :
    (((N : ℝ) ^ 2 + N) * QAlgorithms.frobNorm (complexMatrix A) ≥
      (N : ℝ) ^ 2 * matrixMax A) ∧
    ((N : ℝ) ^ 2 * matrixMax A ≥
      D * Real.sqrt ((Sc : ℝ) * Sr) * matrixMax A) := by
  have hent : ∀ i j, |A i j| ≤ QAlgorithms.frobNorm (complexMatrix A) := by
    intro i j
    have e1 : |A i j| = ‖complexMatrix A i j‖ := by simp [complexMatrix]
    let row : PiLp 2 (fun _ : Fin N => ℂ) := WithLp.toLp 2 (fun j => complexMatrix A i j)
    let full : PiLp 2 (fun _ : Fin N => PiLp 2 (fun _ : Fin N => ℂ)) :=
      WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => complexMatrix A i j))
    have h1 : ‖complexMatrix A i j‖ ≤ ‖row‖ := PiLp.norm_apply_le row j
    have h2 : ‖row‖ ≤ ‖full‖ := PiLp.norm_apply_le full i
    have h3 : QAlgorithms.frobNorm (complexMatrix A) = ‖full‖ := rfl
    linarith
  have hfrob0 : 0 ≤ QAlgorithms.frobNorm (complexMatrix A) :=
    le_trans (abs_nonneg _) (hent ⟨0, hN⟩ ⟨0, hN⟩)
  have hmax0 : 0 ≤ matrixMax A := Aux_FOM44.foldr_nonneg _
  have hmaxle : matrixMax A ≤ QAlgorithms.frobNorm (complexMatrix A) := by
    unfold matrixMax
    apply Aux_FOM44.foldr_le _ _ hfrob0
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    apply Aux_FOM44.foldr_le _ _ hfrob0
    intro a ha
    rw [List.mem_ofFn] at ha
    obtain ⟨j, rfl⟩ := ha
    exact hent i j
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  constructor
  · have k1 := mul_le_mul_of_nonneg_left hmaxle (sq_nonneg (N : ℝ))
    have k2 : 0 ≤ (N : ℝ) * QAlgorithms.frobNorm (complexMatrix A) := mul_nonneg hNR hfrob0
    show (N : ℝ) ^ 2 * matrixMax A ≤ ((N : ℝ) ^ 2 + N) * QAlgorithms.frobNorm (complexMatrix A)
    nlinarith
  · have hcR : (Sc : ℝ) ≤ N := by exact_mod_cast hc
    have hrR : (Sr : ℝ) ≤ N := by exact_mod_cast hr
    have hDR : (D : ℝ) ≤ N := by exact_mod_cast hD
    have hprod : (Sc : ℝ) * Sr ≤ (N : ℝ) * N :=
      mul_le_mul hcR hrR (Nat.cast_nonneg _) hNR
    have hs : Real.sqrt ((Sc : ℝ) * Sr) ≤ N := by
      calc Real.sqrt ((Sc : ℝ) * Sr) ≤ Real.sqrt ((N : ℝ) * N) := Real.sqrt_le_sqrt hprod
        _ = N := Real.sqrt_mul_self hNR
    have hDs : (D : ℝ) * Real.sqrt ((Sc : ℝ) * Sr) ≤ (N : ℝ) ^ 2 := by
      rw [sq]
      exact mul_le_mul hDR hs (Real.sqrt_nonneg _) hNR
    show (D : ℝ) * Real.sqrt ((Sc : ℝ) * Sr) * matrixMax A ≤ (N : ℝ) ^ 2 * matrixMax A
    exact mul_le_mul_of_nonneg_right hDs hmax0
