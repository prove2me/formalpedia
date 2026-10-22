-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.interceptResend
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T23:33:16.328717+00:00
-- url     : https://prove2.me/submissions/3aa13fdf-eedf-4bfd-a60b-b0f42c3472ed

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

namespace CfcDiagH
open Matrix Polynomial

lemma aeval_diag {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℝ) (q : ℝ[X]) :
    aeval (diagonal (fun i => (d i : ℂ))) q = diagonal (fun i => ((q.eval (d i) : ℝ) : ℂ)) := by
  have h1 : diagonal (fun i => (d i : ℂ)) = diagonalAlgHom ℝ (fun i => (d i : ℂ)) := rfl
  rw [h1, aeval_algHom_apply, aeval_pi_apply]
  show diagonal _ = _
  congr 1; funext i
  have : ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) := rfl
  rw [this, aeval_algebraMap_apply_eq_algebraMap_eval]; rfl

lemma cfc_diag {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  set A := diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [hA, IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1; funext i; simp
  set s : Finset ℝ := Finset.univ.image d
  set q : ℝ[X] := Lagrange.interpolate s id f
  have hspec : spectrum ℝ A ⊆ (s : Set ℝ) := by
    intro x hx
    have h2 : (algebraMap ℝ ℂ x) ∈ spectrum ℂ A := (spectrum.algebraMap_mem_iff ℂ).2 hx
    rw [hA, spectrum_diagonal] at h2
    obtain ⟨i, hi⟩ := h2
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    exact ⟨i, by simpa [Complex.ofReal_inj] using hi⟩
  have heq : (spectrum ℝ A).EqOn f (fun x => q.eval x) := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id) f (Set.injOn_id _) (hspec hx)
    simpa [q] using this.symm
  rw [cfc_congr heq, cfc_polynomial q A hsa, hA, aeval_diag]
  congr 1; funext i
  have hi : d i ∈ s := by simp [s]
  have := Lagrange.eval_interpolate_at_node (s := s) (v := id) f (Set.injOn_id _) hi
  simp only [id] at this
  rw [this]

lemma classicalEntropy_eq {I : Type} [Fintype I] [DecidableEq I] (p : I → ℝ) :
    QAlgorithms.Papers.Independent.Claimed50.P08.classicalEntropy p =
      -∑ i, p i * Real.logb 2 (p i) := by
  unfold QAlgorithms.Papers.Independent.Claimed50.P08.classicalEntropy QAlgorithms.vnEntropy
  rw [cfc_diag, trace_diagonal, Complex.re_sum]
  simp

end CfcDiagH

namespace P25IrH
lemma half (x : ℝ) : x / 2 * Real.logb 2 (x / 2) = (x * Real.logb 2 x - x) / 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.logb_div hx (by norm_num), Real.logb_self_eq_one (by norm_num)]; ring
end P25IrH

/-- I.B.5, PDF p.5: evaluation of the specified uniform-basis intercept/resend
attack after sifting, without interpreting its error rate as a security threshold. -/
theorem solution (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (∀ a b e, 0 ≤ irLaw p a b e) ∧
    (∑ a : Bool, ∑ b : Bool, ∑ e : IRRecord, irLaw p a b e) = 1 ∧
    irError p = p/4 ∧ classicalMI (irAE p) = p/2 ∧
    classicalMI (irBE p) = p/2 ∧ p/2 = 2*irError p := by
  have hp0 := hp.1
  have hp1 := hp.2
  refine ⟨fun a b e => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases e with _ | ⟨_ | _, e⟩ <;> simp only [irLaw] <;> (try split_ifs) <;> linarith
  · simp [Fintype.sum_option, Fintype.sum_prod_type, irLaw]; ring
  · simp [irError, Fintype.sum_option, Fintype.sum_prod_type, irLaw]; ring
  · unfold classicalMI
    simp only [CfcDiagH.classicalEntropy_eq]
    simp [Fintype.sum_option, Fintype.sum_prod_type, irAE, irLaw]
    rw [show (1 - p) / 2 + (p / 4 + (p / 16 + p / 16 + (p / 16 + p / 16))) = 1/2 by ring,
      show p / 16 + p / 16 + (p / 16 + p / 16) = p/4 by ring,
      show p / 16 + p / 16 = p/4/2 by ring, P25IrH.half, P25IrH.half, P25IrH.half]
    simp only [Real.logb_one]; ring
  · unfold classicalMI
    simp only [CfcDiagH.classicalEntropy_eq]
    simp [Fintype.sum_option, Fintype.sum_prod_type, irBE, irLaw]
    rw [show (1 - p) / 2 + (p / 4 + (p / 16 + p / 16 + (p / 16 + p / 16))) = 1/2 by ring,
      show p / 16 + p / 16 + (p / 16 + p / 16) = p/4 by ring,
      show p / 16 + p / 16 = p/4/2 by ring, P25IrH.half, P25IrH.half, P25IrH.half]
    simp only [Real.logb_one]; ring
  · simp [irError, Fintype.sum_option, Fintype.sum_prod_type, irLaw]; ring




