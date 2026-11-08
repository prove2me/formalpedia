-- Prove2me | solution 1 for PinningSync.Strong.lemma_2_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:03:17.175636+00:00
-- url     : https://prove2.me/submissions/f4a83793-3d4d-47ba-ac1d-a57d3aa7249e

import Mathlib
import Definitions.Def_PinningSync_Strong_Setting

namespace Aux_PSl29

open Matrix PinningSync.Strong

theorem root_iff {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) :
    (A.charpoly.map Complex.ofRealHom).IsRoot z ↔
      ∃ v : Fin N → ℂ, v ≠ 0 ∧ (A.map Complex.ofRealHom) *ᵥ v = z • v := by
  rw [← Matrix.charpoly_map, Polynomial.IsRoot, Matrix.eval_charpoly,
    ← Matrix.exists_mulVec_eq_zero_iff]
  have hd : ∀ v : Fin N → ℂ, (Matrix.scalar (Fin N) z) *ᵥ v = z • v := by
    intro v; funext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, hd, sub_eq_zero] at h
    exact h.symm
  · rintro ⟨v, hv, h⟩
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, hd, h, sub_self]

end Aux_PSl29

open Matrix PinningSync.Strong Aux_PSl29 in
theorem solution {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : ∀ i j, 0 ≤ A i j) (r : ℝ)
    (hrow : ∀ i, ∑ j, A i j = r) :
    specRad A = infNorm A := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    unfold specRad infNorm
    have hS : ((fun z : ℂ => ‖z‖) '' {z : ℂ | (A.charpoly.map Complex.ofRealHom).IsRoot z}) = ∅ := by
      ext s
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨z, hz, _⟩
      obtain ⟨v, hv, _⟩ := (root_iff A z).mp hz
      exact hv (funext fun i => i.elim0)
    rw [hS, Real.sSup_empty, Real.iSup_of_isEmpty]
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hr0 : 0 ≤ r := by
    rw [← hrow ⟨0, hN⟩]; exact Finset.sum_nonneg (fun j _ => hA _ j)
  have hinf : infNorm A = r := by
    unfold infNorm
    have : ∀ i, ∑ j, |A i j| = r := fun i => by
      rw [← hrow i]; exact Finset.sum_congr rfl (fun j _ => abs_of_nonneg (hA i j))
    simp only [this, ciSup_const]
  rw [hinf]
  unfold specRad
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨(r : ℂ), ?_, ?_⟩
    · rw [Set.mem_setOf_eq, root_iff]
      refine ⟨fun _ => 1, ?_, ?_⟩
      · intro h
        have := congrFun h ⟨0, hN⟩
        simp at this
      · funext i
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, mul_one, Pi.smul_apply,
          smul_eq_mul, Complex.ofRealHom_eq_coe]
        rw [← Complex.ofReal_sum, hrow i]
    · simp [abs_of_nonneg hr0]
  · rintro s ⟨z, hz, rfl⟩
    obtain ⟨v, hv, h⟩ := (root_iff A z).mp hz
    obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => ‖v i‖) Finset.univ_nonempty
    have hvpos : 0 < ‖v i0‖ := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
      have := hi0 k (Finset.mem_univ _)
      have : 0 < ‖v k‖ := norm_pos_iff.mpr hk
      linarith
    have heq := congrFun h i0
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofRealHom_eq_coe] at heq
    have hb : ‖z‖ * ‖v i0‖ ≤ r * ‖v i0‖ := by
      rw [← norm_mul, ← heq]
      calc ‖∑ j, ((A i0 j : ℝ) : ℂ) * v j‖ ≤ ∑ j, ‖((A i0 j : ℝ) : ℂ) * v j‖ :=
            norm_sum_le _ _
        _ = ∑ j, A i0 j * ‖v j‖ := by
            apply Finset.sum_congr rfl; intro j _
            rw [norm_mul]
            simp [abs_of_nonneg (hA i0 j)]
        _ ≤ ∑ j, A i0 j * ‖v i0‖ := by
            apply Finset.sum_le_sum; intro j _
            exact mul_le_mul_of_nonneg_left (hi0 j (Finset.mem_univ _)) (hA i0 j)
        _ = r * ‖v i0‖ := by rw [← Finset.sum_mul, hrow i0]
    exact le_of_mul_le_mul_right hb hvpos
