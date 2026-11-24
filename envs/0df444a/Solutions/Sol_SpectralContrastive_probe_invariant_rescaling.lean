-- Prove2me | solution 1 for SpectralContrastive.probe_invariant_rescaling
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T02:59:19.026047+00:00
-- url     : https://prove2.me/submissions/c11e1328-089c-4eae-a548-9f5ad7a4639d

import Mathlib
import Definitions.Def_SpectralContrastive_Basic

open Matrix
namespace SpectralContrastive

lemma pr_row {X : Type*} [Fintype X] [DecidableEq X] {k r : ℕ}
    (F : Matrix X (Fin k) ℝ) (s : X → ℝ) (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : IsUnit Q.det)
    (B : Matrix (Fin k) (Fin r) ℝ) (x : X) :
    vecMul ((diagonal s * F * Q) x) (Q⁻¹ * B) = s x • vecMul (F x) B := by
  have h1 : (diagonal s * F * Q) x = vecMul (s x • F x) Q := by
    funext j
    simp [Matrix.mul_apply, vecMul, dotProduct, diagonal, mul_assoc]
  rw [h1, vecMul_vecMul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.one_mul,
    smul_vecMul]

theorem probe_invariant_rescaling {Xbar X : Type*} [Fintype Xbar] [Fintype X] [DecidableEq X]
    {k r : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (y : Xbar → Fin r)
    (F : Matrix X (Fin k) ℝ) (s : X → ℝ) (hs : ∀ x, 0 < s x)
    (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : IsUnit Q.det) :
    (∀ (B : Matrix (Fin k) (Fin r) ℝ) (x : X) (i : Fin r),
      (∀ j, vecMul ((diagonal s * F * Q) x) (Q⁻¹ * B) j ≤
          vecMul ((diagonal s * F * Q) x) (Q⁻¹ * B) i) ↔
        (∀ j, vecMul (F x) B j ≤ vecMul (F x) B i)) ∧
    linearProbeError P A y (diagonal s * F * Q) = linearProbeError P A y F := by
  have key : ∀ (B : Matrix (Fin k) (Fin r) ℝ) (x : X) (i j : Fin r),
      vecMul ((diagonal s * F * Q) x) (Q⁻¹ * B) j ≤
          vecMul ((diagonal s * F * Q) x) (Q⁻¹ * B) i ↔ vecMul (F x) B j ≤ vecMul (F x) B i := by
    intro B x i j
    rw [pr_row F s Q hQ B x, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_iff_of_pos_left (hs x)
  have hpred : ∀ (B : Matrix (Fin k) (Fin r) ℝ) (g : X → Fin r),
      IsProbePred (diagonal s * F * Q) (Q⁻¹ * B) g ↔ IsProbePred F B g := by
    intro B g
    unfold IsProbePred
    exact forall_congr' fun x => forall_congr' fun i => key B x (g x) i
  refine ⟨fun B x i => forall_congr' fun j => key B x i j, ?_⟩
  have hpe : ∀ B : Matrix (Fin k) (Fin r) ℝ,
      probeError P A y (diagonal s * F * Q) (Q⁻¹ * B) = probeError P A y F B := by
    intro B
    unfold probeError
    exact Equiv.iSup_congr (Equiv.subtypeEquivRight fun c => and_congr_left' (hpred B c.1))
      (fun _ => rfl)
  have hsurj : Function.Surjective (fun B : Matrix (Fin k) (Fin r) ℝ => Q⁻¹ * B) := by
    intro C
    exact ⟨Q * C, Matrix.nonsing_inv_mul_cancel_left Q C hQ⟩
  unfold linearProbeError
  rw [← hsurj.iInf_comp]
  exact iInf_congr hpe

end SpectralContrastive

open SpectralContrastive in
theorem solution {Xbar X : Type*} [Fintype Xbar] [Fintype X] [DecidableEq X]
    {k r : ℕ} (P : Xbar → ℝ) (A : Xbar → X → ℝ) (y : Xbar → Fin r)
    (F : Matrix X (Fin k) ℝ) (s : X → ℝ) (hs : ∀ x, 0 < s x)
    (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : IsUnit Q.det) :
    (∀ (B : Matrix (Fin k) (Fin r) ℝ) (x : X) (i : Fin r),
      (∀ j, vecMul ((diagonal s * F * Q) x) (Q⁻¹ * B) j ≤
          vecMul ((diagonal s * F * Q) x) (Q⁻¹ * B) i) ↔
        (∀ j, vecMul (F x) B j ≤ vecMul (F x) B i)) ∧
    linearProbeError P A y (diagonal s * F * Q) = linearProbeError P A y F :=
  SpectralContrastive.probe_invariant_rescaling P A y F s hs Q hQ
