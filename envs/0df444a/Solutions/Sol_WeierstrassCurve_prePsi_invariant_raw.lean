-- Prove2me | solution 1 for WeierstrassCurve.prePsi_invariant_raw
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:04:22.141869+00:00
-- url     : https://prove2.me/submissions/bb40cd4e-7452-4e06-9769-230f98a200d9

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_PsiInvariant
import Definitions.Def_WardInvariant
import Theorems.Thm_FLT_EDS_mk_C_injective
import Theorems.Thm_FLT_EDS_mk_psi_eq
import Theorems.Thm_FLT_EDS_invarRel_all
import Definitions.Def_WardConservation

/-! Proofs of the lemmas stated in `Theorems.Thm_EDS_PreDivisionInvariant` and their helpers. -/
open Polynomial

open scoped Polynomial

open FLT.EDS

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R]

public lemma mk_invariant_descended [IsDomain R] (W : WeierstrassCurve R)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (m : ℤ) :
    Affine.CoordinateRing.mk W (C W.Ψ₃ *
        (W.ψ (m + 2) * W.ψ (m - 1) ^ 2 + W.ψ (m + 1) ^ 2 * W.ψ (m - 2) + W.ψ₂ ^ 2 * W.ψ m ^ 3))
      = Affine.CoordinateRing.mk W ((C W.preΨ₄ + W.ψ₂ ^ 4) *
        (W.ψ (m + 1) * W.ψ m * W.ψ (m - 1))) := by
  have hne_norm : ∀ k : ℤ, k ≠ 0 → normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) k ≠ 0 := by
    intro k hk; simpa [WeierstrassCurve.ψ] using hψ_ne k hk
  have hWard := invarRel_all (R := Polynomial (Polynomial R)) W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) hne_norm m
  apply congrArg
  simpa [InvarRel, Nseq, Dseq, WeierstrassCurve.ψ] using hWard

private lemma preΨ_invariant_even [IsDomain R] (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) {m : ℤ} (hm : Even m) :
    W.Ψ₃ * preΨInvN W m = (W.preΨ₄ + W.Ψ₂Sq ^ 2) * preΨInvD W m := by
  have hMk := mk_invariant_descended W hψ_ne m
  have h2sq := Affine.CoordinateRing.mk_ψ₂_sq W
  have ep2 : Even (m + 2) ↔ Even m := by simp [Int.even_add]
  have em2 : Even (m - 2) ↔ Even m := by simp [Int.even_sub]
  have ep1 : Even (m + 1) ↔ ¬ Even m := by rw [Int.even_add]; simp [Int.not_even_one]
  have em1 : Even (m - 1) ↔ ¬ Even m := by rw [Int.even_sub]; simp [Int.not_even_one]
  simp only [map_mul, map_add, map_sub, map_pow, mk_psi_eq, ep2, em2, ep1, em1,
    hm, if_true, if_false, not_true, not_false_iff, mul_one] at hMk
  have hsq_ne : Affine.CoordinateRing.mk W (C W.Ψ₂Sq) ≠ 0 := fun hc =>
    W.Ψ₂Sq_ne_zero h4 (mk_C_injective W (by simpa using hc))
  rw [← h2sq] at hsq_ne
  have hq_ne : Affine.CoordinateRing.mk W W.ψ₂ ≠ 0 := fun h => hsq_ne (by rw [h]; ring)
  apply mk_C_injective W
  simp only [map_mul, map_add, map_pow, map_one, preΨInvN, preΨInvD, if_pos hm, one_mul]
  apply mul_left_cancel₀ hq_ne
  rw [← h2sq]
  linear_combination hMk

private lemma preΨ_invariant_odd [IsDomain R] (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) {m : ℤ} (hm : ¬ Even m) :
    W.Ψ₃ * preΨInvN W m = (W.preΨ₄ + W.Ψ₂Sq ^ 2) * preΨInvD W m := by
  have hMk := mk_invariant_descended W hψ_ne m
  have h2sq := Affine.CoordinateRing.mk_ψ₂_sq W
  have ep2 : Even (m + 2) ↔ Even m := by simp [Int.even_add]
  have em2 : Even (m - 2) ↔ Even m := by simp [Int.even_sub]
  have ep1 : Even (m + 1) ↔ ¬ Even m := by rw [Int.even_add]; simp [Int.not_even_one]
  have em1 : Even (m - 1) ↔ ¬ Even m := by rw [Int.even_sub]; simp [Int.not_even_one]
  simp only [map_mul, map_add, map_sub, map_pow, mk_psi_eq, ep2, em2, ep1, em1,
    hm, if_true, if_false, not_true, not_false_iff, mul_one] at hMk
  have hq2_ne : Affine.CoordinateRing.mk W W.ψ₂ ^ 2 ≠ 0 := by
    rw [h2sq]
    exact fun hc => W.Ψ₂Sq_ne_zero h4 (mk_C_injective W (by simpa using hc))
  apply mk_C_injective W
  simp only [map_mul, map_add, map_pow, map_one, preΨInvN, preΨInvD, if_neg hm, one_mul]
  apply mul_left_cancel₀ hq2_ne
  rw [← h2sq]
  linear_combination hMk

public lemma preΨ_invariant [IsDomain R] (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (m : ℤ) :
    W.Ψ₃ * preΨInvN W m = (W.preΨ₄ + W.Ψ₂Sq ^ 2) * preΨInvD W m := by
  by_cases hm : Even m
  · exact preΨ_invariant_even W h4 hψ_ne hm
  · exact preΨ_invariant_odd W h4 hψ_ne hm

/-- Public raw form of `preΨ_invariant` (unfolded `preΨInvN`/`preΨInvD`) for downstream use. -/
theorem _root_.solution [IsDomain R] (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (m : ℤ) :
    W.Ψ₃ * (W.preΨ (m + 2) * W.preΨ (m - 1) ^ 2 + W.preΨ (m + 1) ^ 2 * W.preΨ (m - 2)
            + (if Even m then W.Ψ₂Sq ^ 2 else 1) * W.preΨ m ^ 3)
      = (W.preΨ₄ + W.Ψ₂Sq ^ 2) * (W.preΨ (m + 1) * W.preΨ m * W.preΨ (m - 1)) := by
  simpa [preΨInvN, preΨInvD] using preΨ_invariant W h4 hψ_ne m

end

end WeierstrassCurve
