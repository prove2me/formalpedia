-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P30.separableCone_stability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T10:14:52.140038+00:00
-- url     : https://prove2.me/submissions/3ce58c0a-7031-44de-b35e-1256ed432635

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P30

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section x8

set_option linter.unusedSectionVars false

variable {I J K L : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
  [DecidableEq I] [DecidableEq J]

omit [Fintype K] in
lemma x8_map_eq (F : MatrixMap I K) (A : Matrix I I ℂ) (k k' : K) :
    F A k k' = ∑ i, ∑ a, A i a * F (Matrix.single i a 1) k k' := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  rw [show Matrix.single i a (A i a) = A i a • Matrix.single i a (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, Matrix.smul_apply, smul_eq_mul]

lemma x8_tensor_kron (F : MatrixMap I K) (G : MatrixMap J L)
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    tensorMap F G (Matrix.kronecker A B) = Matrix.kronecker (F A) (G B) := by
  ext ⟨k, l⟩ ⟨k', l'⟩
  simp only [tensorMap, Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, smul_eq_mul, x8_map_eq F A, x8_map_eq G B]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun b _ => ?_
  ring

def x8T (F : MatrixMap I K) (G : MatrixMap J L) :
    Matrix (I × J) (I × J) ℂ →ₗ[ℂ] Matrix (K × L) (K × L) ℂ where
  toFun := tensorMap F G
  map_add' X Y := by
    simp only [tensorMap, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [tensorMap, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul,
      RingHom.id_apply]

lemma x8_tensor_sum (F : MatrixMap I K) (G : MatrixMap J L) {q : ℕ}
    (c : Fin q → ℂ) (X : Fin q → Matrix (I × J) (I × J) ℂ) :
    tensorMap F G (∑ j, c j • X j) = ∑ j, c j • tensorMap F G (X j) := by
  have h := map_sum (x8T F G) (fun j => c j • X j) Finset.univ
  simp only [map_smul] at h
  exact h

omit [DecidableEq I] [DecidableEq J] in
lemma x8_normalize {M : Type*} [Fintype M] [Nonempty M] (P : Matrix M M ℂ)
    (hP : P.PosSemidef) : ∃ t : ℝ, 0 ≤ t ∧ ∃ D : Matrix M M ℂ, IsDensityMatrix D ∧
      P = (t : ℂ) • D := by
  classical
  by_cases h0 : P.trace = 0
  · have hz : P = 0 := (hP.trace_eq_zero_iff).mp h0
    refine ⟨0, le_rfl, ((Fintype.card M : ℂ)⁻¹) • (1 : Matrix M M ℂ), ⟨?_, ?_⟩, by simp [hz]⟩
    · refine Matrix.PosSemidef.one.smul ?_
      have : (0 : ℂ) ≤ (((Fintype.card M : ℝ)⁻¹ : ℝ) : ℂ) :=
        Complex.zero_le_real.mpr (by positivity)
      simpa using this
    · rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
      have : (Fintype.card M : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      field_simp
  · have htn : 0 ≤ P.trace := hP.trace_nonneg
    obtain ⟨t, ht⟩ : ∃ t : ℝ, (t : ℂ) = P.trace :=
      ⟨P.trace.re, (Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp htn).2))⟩
    have htc : (t : ℂ) ≠ 0 := by rw [ht]; exact h0
    have htpos : 0 ≤ t := by
      have : (0 : ℂ) ≤ (t : ℂ) := ht ▸ htn
      exact_mod_cast this
    refine ⟨t, htpos, ((t : ℂ)⁻¹) • P, ⟨?_, ?_⟩, ?_⟩
    · refine hP.smul ?_
      have : (0 : ℝ) ≤ t⁻¹ := inv_nonneg.mpr htpos
      exact_mod_cast (Complex.zero_le_real.mpr this)
    · rw [Matrix.trace_smul, smul_eq_mul, ← ht]; field_simp
    · rw [smul_smul, mul_inv_cancel₀ htc, one_smul]

end x8

theorem x8_main {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
    [DecidableEq I] [DecidableEq J]
    (F : MatrixMap I K) (G : MatrixMap J L)
    (hF : IsPositiveMap F) (hG : IsPositiveMap G) :
    ∀ X : Matrix (I × J) (I × J) ℂ, Entanglement.IsSeparablePositive X →
      Entanglement.IsSeparablePositive (tensorMap F G X) := by
  rintro X ⟨q, w, A, B, hw, hAB, rfl⟩
  have hFA : ∀ j, ∃ t : ℝ, 0 ≤ t ∧ ∃ D : Matrix K K ℂ, IsDensityMatrix D ∧
      F (A j) = (t : ℂ) • D := fun j => x8_normalize _ (hF _ (hAB j).1.1)
  have hGB : ∀ j, ∃ t : ℝ, 0 ≤ t ∧ ∃ D : Matrix L L ℂ, IsDensityMatrix D ∧
      G (B j) = (t : ℂ) • D := fun j => x8_normalize _ (hG _ (hAB j).2.1)
  choose s hs C hC hFC using hFA
  choose t ht D hD hGD using hGB
  refine ⟨q, fun j => w j * s j * t j, C, D, fun j => ?_, fun j => ⟨hC j, hD j⟩, ?_⟩
  · exact mul_nonneg (mul_nonneg (hw j) (hs j)) (ht j)
  · rw [x8_tensor_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [x8_tensor_kron, hFC, hGD]
    ext p r
    simp only [Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, smul_eq_mul]
    push_cast
    ring

end QAlgorithms.Papers.Independent.Information100.P30

open QAlgorithms.Papers.Independent.Information100.P30 in
theorem solution {I J K L : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty L]
    [DecidableEq I] [DecidableEq J]
    (F : MatrixMap I K) (G : MatrixMap J L)
    (hF : IsPositiveMap F) (hG : IsPositiveMap G) :
    ∀ X : Matrix (I × J) (I × J) ℂ, QAlgorithms.Entanglement.IsSeparablePositive X →
      QAlgorithms.Entanglement.IsSeparablePositive (tensorMap F G X) :=
  x8_main F G hF hG
