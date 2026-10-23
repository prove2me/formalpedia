-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.genericKrausGram
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:53:26.170182+00:00
-- url     : https://prove2.me/submissions/d385650a-2fa5-404c-9400-dfb45ab410cd

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma X7_kraus_entry {d n : ℕ} (K : Fin n → Mat d) (X : Mat d) (r s : Fin d) :
    krausApply K X r s = ∑ a, ∑ p, ∑ q, K a r p * X p q * conj (K a s q) := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

lemma X7_kraus_unit {d n : ℕ} (K : Fin n → Mat d) (i j r s : Fin d) :
    krausApply K (matrixUnit i j) r s = inner ℂ (krausVector K s j) (krausVector K r i) := by
  rw [X7_kraus_entry, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [matrixUnit, Matrix.single_apply, krausVector, PiLp.toLp_apply, RCLike.inner_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro q _ hq; simp [Ne.symm hq]
    · simp
  · intro p _ hp; simp [Ne.symm hp]
  · simp

lemma X7_pop {d n : ℕ} (K : Fin n → Mat d) (r i : Fin d) :
    population (krausApply K) r i = ‖krausVector K r i‖ ^ 2 := by
  unfold population
  rw [X7_kraus_unit, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma X7_collinear_iff {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {v w : V}
    (hv : v ≠ 0) (hw : w ≠ 0) : Collinear v w ↔ ∃ c : ℂ, c ≠ 0 ∧ v = c • w := by
  constructor
  · rintro ⟨a, b, hab, h⟩
    have ha : a ≠ 0 := by
      rintro rfl
      have hb : b ≠ 0 := hab.resolve_left (by simp)
      simp only [zero_smul, zero_add] at h
      exact hw ((smul_eq_zero.mp h).resolve_left hb)
    refine ⟨-b / a, ?_, ?_⟩
    · intro h0
      have hb : b = 0 := by
        rcases div_eq_zero_iff.mp h0 with h1 | h1
        · exact neg_eq_zero.mp h1
        · exact absurd h1 ha
      subst hb
      simp only [zero_smul, add_zero] at h
      exact hv ((smul_eq_zero.mp h).resolve_left ha)
    · have : a • v = -(b • w) := eq_neg_of_add_eq_zero_left h
      calc v = a⁻¹ • (a • v) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        _ = (-b / a) • w := by rw [this, smul_neg, smul_smul, ← neg_smul]; congr 1; field_simp
  · rintro ⟨c, _, h⟩
    exact ⟨1, -c, Or.inl one_ne_zero, by rw [h, one_smul, neg_smul, add_neg_cancel]⟩

end

end QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44 in
theorem solution {d n : ℕ} (hd : 0 < d) (K : Fin n → Mat d) :
    (∀ r i, (krausApply K (matrixUnit i i) r r : ℂ) =
      (‖krausVector K r i‖ ^ 2 : ℝ)) ∧
    (∀ i j r s, krausApply K (matrixUnit i j) r s =
      inner ℂ (krausVector K s j) (krausVector K r i)) ∧
    (∀ i j r s, ‖krausApply K (matrixUnit i j) r s‖ ≤
      Real.sqrt (population (krausApply K) r i * population (krausApply K) s j)) ∧
    (∀ i j r s, krausVector K r i ≠ 0 → krausVector K s j ≠ 0 →
      (‖krausApply K (matrixUnit i j) r s‖ =
        Real.sqrt (population (krausApply K) r i * population (krausApply K) s j) ↔
          QAlgorithms.Papers.Independent.Information100.P44.Collinear (krausVector K r i) (krausVector K s j))) := by
  have hsq : ∀ i j r s, Real.sqrt (population (krausApply K) r i * population (krausApply K) s j) =
      ‖krausVector K s j‖ * ‖krausVector K r i‖ := by
    intro i j r s
    rw [X7_pop, X7_pop, ← mul_pow, Real.sqrt_sq (by positivity), mul_comm]
  refine ⟨fun r i => ?_, fun i j r s => X7_kraus_unit K i j r s, fun i j r s => ?_,
    fun i j r s hv hw => ?_⟩
  · rw [X7_kraus_unit, inner_self_eq_norm_sq_to_K]; norm_cast
  · rw [hsq, X7_kraus_unit]; exact norm_inner_le_norm _ _
  · rw [hsq, X7_kraus_unit, norm_inner_eq_norm_iff hw hv, X7_collinear_iff hv hw]

end
